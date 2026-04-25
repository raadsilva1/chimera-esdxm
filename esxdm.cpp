#include <X11/Xauth.h>
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/Xft/Xft.h>
#include <X11/keysym.h>
#include <security/pam_appl.h>

#include <cerrno>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstring>
#include <fcntl.h>
#include <grp.h>
#include <pwd.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <sys/random.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdlib>
#include <filesystem>
#include <functional>
#include <initializer_list>
#include <limits>
#include <cstdio>
#include <ctime>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <stdexcept>
#include <utility>
#include <vector>

extern char **environ;

namespace {

inline int x_default_screen(Display *dpy) { return DefaultScreen(dpy); }
inline Window x_root_window(Display *dpy, int screen) { return RootWindow(dpy, screen); }
inline Colormap x_default_colormap(Display *dpy, int screen) { return DefaultColormap(dpy, screen); }
inline int x_connection_number(Display *dpy) { return ConnectionNumber(dpy); }
inline unsigned int x_display_width(Display *dpy, int screen) { return DisplayWidth(dpy, screen); }
inline unsigned int x_display_height(Display *dpy, int screen) { return DisplayHeight(dpy, screen); }
inline int x_default_depth(Display *dpy, int screen) { return DefaultDepth(dpy, screen); }
inline Visual *x_default_visual(Display *dpy, int screen) { return DefaultVisual(dpy, screen); }

constexpr const char *kVersion = "esxdm 0.1";
constexpr const char *kPamService = "esxdm";
constexpr const char *kDisplayDefault = ":0";
constexpr int kDefaultVt = 7;
constexpr int kMaxRetries = 2;
constexpr size_t kMaxUsername = 128;
constexpr size_t kMaxPassword = 512;

struct Options {
    std::string display = kDisplayDefault;
    std::string display_number = "0";
    int vt = kDefaultVt;
    std::string xorg = "/usr/bin/Xorg";
    std::string log_path = "/var/log/esxdm.log";
    std::string runtime_dir = "/run/esxdm";
    int retry_limit = 2;
    bool fallback_session = true;
};

enum class LogLevel { Info, Warn, Error };

static std::string errno_text(int err) {
    return std::string(std::strerror(err));
}

static void secure_zero(void *ptr, size_t len) {
    volatile unsigned char *p = static_cast<volatile unsigned char *>(ptr);
    while (len-- > 0) {
        *p++ = 0;
    }
}

static bool write_all(int fd, const char *data, size_t len) {
    while (len > 0) {
        ssize_t rc = ::write(fd, data, len);
        if (rc < 0) {
            if (errno == EINTR) {
                continue;
            }
            return false;
        }
        data += static_cast<size_t>(rc);
        len -= static_cast<size_t>(rc);
    }
    return true;
}

static std::string utc_timestamp() {
    using clock = std::chrono::system_clock;
    auto now = clock::now();
    std::time_t t = clock::to_time_t(now);
    std::tm tm {};
    gmtime_r(&t, &tm);
    char buf[32];
    if (std::strftime(buf, sizeof(buf), "%Y-%m-%dT%H:%M:%SZ", &tm) == 0) {
        return "1970-01-01T00:00:00Z";
    }
    return std::string(buf);
}

static std::string escape_token(std::string_view input) {
    std::string out;
    out.reserve(input.size() * 2);
    auto safe = [](unsigned char c) {
        return std::isalnum(c) || c == '_' || c == '-' || c == '.' || c == '/' ||
               c == ':' || c == '+' || c == '=' || c == '@';
    };
    char buf[4];
    for (unsigned char c : input) {
        if (safe(c)) {
            out.push_back(static_cast<char>(c));
        } else {
            std::snprintf(buf, sizeof(buf), "%%%02X", c);
            out.append(buf);
        }
    }
    return out;
}

static bool parse_int(std::string_view text, int &out) {
    if (text.empty()) {
        return false;
    }
    char *end = nullptr;
    errno = 0;
    std::string owned(text);
    long value = std::strtol(owned.c_str(), &end, 10);
    if (errno != 0 || !end || *end != '\0') {
        return false;
    }
    if (value < std::numeric_limits<int>::min() || value > std::numeric_limits<int>::max()) {
        return false;
    }
    out = static_cast<int>(value);
    return true;
}

static bool parse_display_number(const std::string &display, std::string &number) {
    auto colon = display.find(':');
    if (colon == std::string::npos) {
        return false;
    }
    size_t start = colon + 1;
    size_t end = start;
    while (end < display.size() && std::isdigit(static_cast<unsigned char>(display[end]))) {
        ++end;
    }
    if (end == start) {
        return false;
    }
    number = display.substr(start, end - start);
    return true;
}

static bool is_regular_executable(const std::string &path) {
    struct stat st {};
    if (::stat(path.c_str(), &st) != 0) {
        return false;
    }
    if (!S_ISREG(st.st_mode)) {
        return false;
    }
    return (st.st_mode & (S_IXUSR | S_IXGRP | S_IXOTH)) != 0;
}

static bool path_exists(const std::string &path) {
    struct stat st {};
    return ::stat(path.c_str(), &st) == 0;
}

static bool read_file_pid(const std::string &path, pid_t &pid_out) {
    int fd = ::open(path.c_str(), O_RDONLY | O_CLOEXEC);
    if (fd < 0) {
        return false;
    }
    char buf[64];
    ssize_t n = ::read(fd, buf, sizeof(buf) - 1);
    ::close(fd);
    if (n <= 0) {
        return false;
    }
    buf[n] = '\0';
    char *end = nullptr;
    errno = 0;
    long value = std::strtol(buf, &end, 10);
    if (errno != 0 || end == buf) {
        return false;
    }
    if (value <= 0 || value > std::numeric_limits<pid_t>::max()) {
        return false;
    }
    pid_out = static_cast<pid_t>(value);
    return true;
}

static bool make_pipe_cloexec(int pipefd[2]) {
    if (::pipe(pipefd) != 0) {
        return false;
    }
    for (int i = 0; i < 2; ++i) {
        int fd = pipefd[i];
        int flags = ::fcntl(fd, F_GETFD);
        if (flags < 0) {
            ::close(pipefd[0]);
            ::close(pipefd[1]);
            return false;
        }
        if (::fcntl(fd, F_SETFD, flags | FD_CLOEXEC) != 0) {
            ::close(pipefd[0]);
            ::close(pipefd[1]);
            return false;
        }
    }
    return true;
}

static bool fd_is_kept(int fd, const std::vector<int> &keep) {
    return std::find(keep.begin(), keep.end(), fd) != keep.end();
}

static void close_fds_except(const std::vector<int> &keep) {
    long maxfd = ::sysconf(_SC_OPEN_MAX);
    if (maxfd < 0) {
        maxfd = 1024;
    }
    for (int fd = 3; fd < maxfd; ++fd) {
        if (!fd_is_kept(fd, keep)) {
            ::close(fd);
        }
    }
}

static std::string join_kv(std::initializer_list<std::pair<const char *, std::string>> kv) {
    std::string out;
    for (const auto &[key, value] : kv) {
        out.push_back(' ');
        out.append(key);
        out.push_back('=');
        out.append(escape_token(value));
    }
    return out;
}

class Logger {
public:
    explicit Logger(const std::string &path) {
        fd_ = ::open(path.c_str(), O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC | O_NOFOLLOW, 0600);
        if (fd_ < 0) {
            std::fprintf(stderr, "esxdm: failed to open log file %s: %s\n", path.c_str(), errno_text(errno).c_str());
        }
    }

    void info(const std::string &component, const std::string &message,
              std::initializer_list<std::pair<const char *, std::string>> kv = {}) {
        log(LogLevel::Info, component, message, kv);
    }

    void warn(const std::string &component, const std::string &message,
              std::initializer_list<std::pair<const char *, std::string>> kv = {}) {
        log(LogLevel::Warn, component, message, kv);
    }

    void error(const std::string &component, const std::string &message,
               std::initializer_list<std::pair<const char *, std::string>> kv = {}) {
        log(LogLevel::Error, component, message, kv);
    }

private:
    int fd_{-1};

    void log(LogLevel level, const std::string &component, const std::string &message,
             std::initializer_list<std::pair<const char *, std::string>> kv) {
        std::string line = utc_timestamp();
        line.push_back(' ');
        line.append(level == LogLevel::Info ? "info" : (level == LogLevel::Warn ? "warn" : "error"));
        line.push_back(' ');
        line.append(escape_token(component));
        line.push_back(' ');
        line.append(std::to_string(::getpid()));
        line.push_back(' ');
        line.append(escape_token(message));
        line.append(join_kv(kv));
        line.push_back('\n');
        if (fd_ >= 0) {
            (void)write_all(fd_, line.c_str(), line.size());
        }
        (void)write_all(STDERR_FILENO, line.c_str(), line.size());
    }
};

class FdHandle {
public:
    FdHandle() = default;
    explicit FdHandle(int fd) : fd_(fd) {}
    ~FdHandle() { reset(); }
    FdHandle(const FdHandle &) = delete;
    FdHandle &operator=(const FdHandle &) = delete;
    FdHandle(FdHandle &&other) noexcept : fd_(other.fd_) { other.fd_ = -1; }
    FdHandle &operator=(FdHandle &&other) noexcept {
        if (this != &other) {
            reset();
            fd_ = other.fd_;
            other.fd_ = -1;
        }
        return *this;
    }
    int get() const { return fd_; }
    explicit operator bool() const { return fd_ >= 0; }
    int release() {
        int fd = fd_;
        fd_ = -1;
        return fd;
    }
    void reset(int fd = -1) {
        if (fd_ >= 0) {
            ::close(fd_);
        }
        fd_ = fd;
    }

private:
    int fd_{-1};
};

class DisplayHandle {
public:
    DisplayHandle() = default;
    explicit DisplayHandle(Display *display) : display_(display) {}
    ~DisplayHandle() { reset(); }
    DisplayHandle(const DisplayHandle &) = delete;
    DisplayHandle &operator=(const DisplayHandle &) = delete;
    DisplayHandle(DisplayHandle &&other) noexcept : display_(other.display_) { other.display_ = nullptr; }
    DisplayHandle &operator=(DisplayHandle &&other) noexcept {
        if (this != &other) {
            reset();
            display_ = other.display_;
            other.display_ = nullptr;
        }
        return *this;
    }
    Display *get() const { return display_; }
    explicit operator bool() const { return display_ != nullptr; }
    void reset(Display *display = nullptr) {
        if (display_) {
            ::XCloseDisplay(display_);
        }
        display_ = display;
    }
    Display *release() {
        Display *d = display_;
        display_ = nullptr;
        return d;
    }

private:
    Display *display_{nullptr};
};

class WindowHandle {
public:
    WindowHandle() = default;
    WindowHandle(Display *display, Window window) : display_(display), window_(window) {}
    ~WindowHandle() { reset(); }
    WindowHandle(const WindowHandle &) = delete;
    WindowHandle &operator=(const WindowHandle &) = delete;
    WindowHandle(WindowHandle &&other) noexcept : display_(other.display_), window_(other.window_) {
        other.display_ = nullptr;
        other.window_ = 0;
    }
    WindowHandle &operator=(WindowHandle &&other) noexcept {
        if (this != &other) {
            reset();
            display_ = other.display_;
            window_ = other.window_;
            other.display_ = nullptr;
            other.window_ = 0;
        }
        return *this;
    }
    Window get() const { return window_; }
    Window release() {
        Window w = window_;
        display_ = nullptr;
        window_ = 0;
        return w;
    }
    void reset() {
        if (display_ && window_) {
            ::XDestroyWindow(display_, window_);
        }
        display_ = nullptr;
        window_ = 0;
    }

private:
    Display *display_{nullptr};
    Window window_{0};
};

class GCHandle {
public:
    GCHandle() = default;
    GCHandle(Display *display, GC gc) : display_(display), gc_(gc) {}
    ~GCHandle() { reset(); }
    GCHandle(const GCHandle &) = delete;
    GCHandle &operator=(const GCHandle &) = delete;
    GCHandle(GCHandle &&other) noexcept : display_(other.display_), gc_(other.gc_) {
        other.display_ = nullptr;
        other.gc_ = nullptr;
    }
    GCHandle &operator=(GCHandle &&other) noexcept {
        if (this != &other) {
            reset();
            display_ = other.display_;
            gc_ = other.gc_;
            other.display_ = nullptr;
            other.gc_ = nullptr;
        }
        return *this;
    }
    GC get() const { return gc_; }
    GC release() {
        GC g = gc_;
        display_ = nullptr;
        gc_ = nullptr;
        return g;
    }
    void reset() {
        if (display_ && gc_) {
            ::XFreeGC(display_, gc_);
        }
        display_ = nullptr;
        gc_ = nullptr;
    }

private:
    Display *display_{nullptr};
    GC gc_{nullptr};
};

class FontHandle {
public:
    FontHandle() = default;
    FontHandle(Display *display, XFontStruct *font) : display_(display), font_(font) {}
    ~FontHandle() { reset(); }
    FontHandle(const FontHandle &) = delete;
    FontHandle &operator=(const FontHandle &) = delete;
    FontHandle(FontHandle &&other) noexcept : display_(other.display_), font_(other.font_) {
        other.display_ = nullptr;
        other.font_ = nullptr;
    }
    FontHandle &operator=(FontHandle &&other) noexcept {
        if (this != &other) {
            reset();
            display_ = other.display_;
            font_ = other.font_;
            other.display_ = nullptr;
            other.font_ = nullptr;
        }
        return *this;
    }
    XFontStruct *get() const { return font_; }
    XFontStruct *release() {
        XFontStruct *font = font_;
        display_ = nullptr;
        font_ = nullptr;
        return font;
    }
    void reset() {
        if (display_ && font_) {
            ::XFreeFont(display_, font_);
        }
        display_ = nullptr;
        font_ = nullptr;
    }

private:
    Display *display_{nullptr};
    XFontStruct *font_{nullptr};
};

class XftFontHandle {
public:
    XftFontHandle() = default;
    XftFontHandle(Display *display, XftFont *font) : display_(display), font_(font) {}
    ~XftFontHandle() { reset(); }
    XftFontHandle(const XftFontHandle &) = delete;
    XftFontHandle &operator=(const XftFontHandle &) = delete;
    XftFontHandle(XftFontHandle &&other) noexcept : display_(other.display_), font_(other.font_) {
        other.display_ = nullptr;
        other.font_ = nullptr;
    }
    XftFontHandle &operator=(XftFontHandle &&other) noexcept {
        if (this != &other) {
            reset();
            display_ = other.display_;
            font_ = other.font_;
            other.display_ = nullptr;
            other.font_ = nullptr;
        }
        return *this;
    }
    XftFont *get() const { return font_; }
    void reset(Display *display = nullptr, XftFont *font = nullptr) {
        if (display_ && font_) {
            XftFontClose(display_, font_);
        }
        display_ = display;
        font_ = font;
    }
    XftFont *release() {
        XftFont *font = font_;
        display_ = nullptr;
        font_ = nullptr;
        return font;
    }

private:
    Display *display_{nullptr};
    XftFont *font_{nullptr};
};

class XftDrawHandle {
public:
    XftDrawHandle() = default;
    XftDrawHandle(Display *display, Drawable drawable, Visual *visual, Colormap colormap)
        : draw_(XftDrawCreate(display, drawable, visual, colormap)) {}
    ~XftDrawHandle() { reset(); }
    XftDrawHandle(const XftDrawHandle &) = delete;
    XftDrawHandle &operator=(const XftDrawHandle &) = delete;
    XftDrawHandle(XftDrawHandle &&other) noexcept : draw_(other.draw_) {
        other.draw_ = nullptr;
    }
    XftDrawHandle &operator=(XftDrawHandle &&other) noexcept {
        if (this != &other) {
            reset();
            draw_ = other.draw_;
            other.draw_ = nullptr;
        }
        return *this;
    }
    XftDraw *get() const { return draw_; }
    explicit operator bool() const { return draw_ != nullptr; }
    void reset(XftDraw *draw = nullptr) {
        if (draw_) {
            XftDrawDestroy(draw_);
        }
        draw_ = draw;
    }
    XftDraw *release() {
        XftDraw *draw = draw_;
        draw_ = nullptr;
        return draw;
    }

private:
    XftDraw *draw_{nullptr};
};

class PamHandle {
public:
    PamHandle() = default;
    ~PamHandle() { reset(); }
    PamHandle(const PamHandle &) = delete;
    PamHandle &operator=(const PamHandle &) = delete;
    PamHandle(PamHandle &&other) noexcept : handle_(other.handle_) { other.handle_ = nullptr; }
    PamHandle &operator=(PamHandle &&other) noexcept {
        if (this != &other) {
            reset();
            handle_ = other.handle_;
            other.handle_ = nullptr;
        }
        return *this;
    }
    pam_handle_t *get() const { return handle_; }
    pam_handle_t **out() { return &handle_; }
    explicit operator bool() const { return handle_ != nullptr; }
    void reset(int status = PAM_SUCCESS) {
        if (handle_) {
            (void)pam_end(handle_, status);
        }
        handle_ = nullptr;
    }

private:
    pam_handle_t *handle_{nullptr};
};

class RuntimeDir {
public:
    RuntimeDir(std::string root, std::string display_number)
        : root_(std::move(root)), display_number_(std::move(display_number)) {}

    const std::string &root() const { return root_; }

    std::string root_auth_path() const {
        return root_ + "/xauth-:" + display_number_;
    }

    std::string user_dir(uid_t uid) const {
        return root_ + "/user-" + std::to_string(uid);
    }

    std::string user_auth_path(uid_t uid) const {
        return user_dir(uid) + "/Xauthority";
    }

    std::string display_lock_path() const {
        return "/tmp/.X" + display_number_ + "-lock";
    }

    std::string display_socket_path() const {
        return "/tmp/.X11-unix/X" + display_number_;
    }

    bool ensure_root(Logger &log) const {
        struct stat st {};
        if (::stat(root_.c_str(), &st) == 0) {
            if (!S_ISDIR(st.st_mode)) {
                log.error("runtime", "runtime_path_not_directory", {{"path", root_}});
                return false;
            }
            if (st.st_uid != 0 || st.st_gid != 0) {
                log.error("runtime", "runtime_path_wrong_owner", {{"path", root_}});
                return false;
            }
            if ((st.st_mode & 0002) != 0) {
                log.error("runtime", "runtime_path_world_writable", {{"path", root_}});
                return false;
            }
            if ((st.st_mode & 0777) != 0711) {
                if (::chmod(root_.c_str(), 0711) != 0) {
                    log.error("runtime", "runtime_fixup_failed", {{"path", root_}, {"errno", errno_text(errno)}});
                    return false;
                }
            }
            return true;
        }
        if (errno != ENOENT) {
            log.error("runtime", "runtime_stat_failed", {{"path", root_}, {"errno", errno_text(errno)}});
            return false;
        }
        if (::mkdir(root_.c_str(), 0711) != 0) {
            log.error("runtime", "runtime_mkdir_failed", {{"path", root_}, {"errno", errno_text(errno)}});
            return false;
        }
        if (::chmod(root_.c_str(), 0711) != 0 || ::chown(root_.c_str(), 0, 0) != 0) {
            log.error("runtime", "runtime_fixup_failed", {{"path", root_}, {"errno", errno_text(errno)}});
            return false;
        }
        return true;
    }

    bool ensure_user_dir(uid_t uid, gid_t gid, Logger &log) const {
        std::string dir = user_dir(uid);
        struct stat st {};
        if (::stat(dir.c_str(), &st) == 0) {
            if (!S_ISDIR(st.st_mode)) {
                log.error("runtime", "user_path_not_directory", {{"path", dir}});
                return false;
            }
            if (st.st_uid != uid || st.st_gid != gid) {
                log.error("runtime", "user_path_wrong_owner", {{"path", dir}});
                return false;
            }
            if ((st.st_mode & 0022) != 0) {
                log.error("runtime", "user_path_world_writable", {{"path", dir}});
                return false;
            }
            return true;
        }
        if (errno != ENOENT) {
            log.error("runtime", "user_stat_failed", {{"path", dir}, {"errno", errno_text(errno)}});
            return false;
        }
        if (::mkdir(dir.c_str(), 0700) != 0) {
            log.error("runtime", "user_mkdir_failed", {{"path", dir}, {"errno", errno_text(errno)}});
            return false;
        }
        if (::chmod(dir.c_str(), 0700) != 0 || ::chown(dir.c_str(), uid, gid) != 0) {
            log.error("runtime", "user_fixup_failed", {{"path", dir}, {"errno", errno_text(errno)}});
            return false;
        }
        return true;
    }

    bool cleanup_user(uid_t uid, Logger &log) const {
        std::string file = user_auth_path(uid);
        if (::unlink(file.c_str()) != 0 && errno != ENOENT) {
            log.warn("runtime", "user_auth_unlink_failed", {{"path", file}, {"errno", errno_text(errno)}});
            return false;
        }
        std::string dir = user_dir(uid);
        if (::rmdir(dir.c_str()) != 0 && errno != ENOENT && errno != ENOTEMPTY) {
            log.warn("runtime", "user_dir_rmdir_failed", {{"path", dir}, {"errno", errno_text(errno)}});
            return false;
        }
        return true;
    }

    bool cleanup_root_auth(Logger &log) const {
        std::string file = root_auth_path();
        if (::unlink(file.c_str()) != 0 && errno != ENOENT) {
            log.warn("runtime", "root_auth_unlink_failed", {{"path", file}, {"errno", errno_text(errno)}});
            return false;
        }
        return true;
    }

    bool ensure_display_lock_clear(Logger &log) const {
        const std::string lock_path = display_lock_path();
        pid_t pid = -1;
        if (!path_exists(lock_path)) {
            return true;
        }
        if (read_file_pid(lock_path, pid)) {
            if (pid > 0 && (::kill(pid, 0) == 0 || errno == EPERM)) {
                log.error("runtime", "display_lock_active", {{"path", lock_path}, {"pid", std::to_string(pid)}});
                return false;
            }
        }
        if (::unlink(lock_path.c_str()) != 0 && errno != ENOENT) {
            log.warn("runtime", "display_lock_unlink_failed", {{"path", lock_path}, {"errno", errno_text(errno)}});
        }
        const std::string socket_path = display_socket_path();
        if (path_exists(socket_path)) {
            if (::unlink(socket_path.c_str()) != 0 && errno != ENOENT) {
                log.warn("runtime", "display_socket_unlink_failed", {{"path", socket_path}, {"errno", errno_text(errno)}});
            }
        }
        return true;
    }

private:
    std::string root_;
    std::string display_number_;
};

class XAuthority {
public:
    XAuthority(std::string display, std::string display_number)
        : display_(std::move(display)), display_number_(std::move(display_number)) {}

    bool generate(Logger &log) {
        return generate_cookie(log);
    }

    const std::array<unsigned char, 16> &cookie() const { return cookie_; }

    bool write_root(const RuntimeDir &runtime, Logger &log) const {
        return write_auth(runtime.root_auth_path(), 0, 0, log);
    }

    bool write_user(const RuntimeDir &runtime, uid_t uid, gid_t gid, Logger &log) const {
        return write_auth(runtime.user_auth_path(uid), uid, gid, log);
    }

private:
    std::string display_;
    std::string display_number_;
    std::array<unsigned char, 16> cookie_{};

    bool generate_cookie(Logger &log) {
        secure_zero(cookie_.data(), cookie_.size());
        ssize_t n = ::getrandom(cookie_.data(), cookie_.size(), 0);
        if (n == static_cast<ssize_t>(cookie_.size())) {
            return true;
        }
        if (!(n < 0 && (errno == ENOSYS || errno == EAGAIN || errno == EINTR))) {
            if (n >= 0) {
                log.warn("xauthority", "getrandom_short_read", {{"read", std::to_string(n)}});
            } else {
                log.warn("xauthority", "getrandom_failed", {{"errno", errno_text(errno)}});
            }
        }
        int fd = ::open("/dev/urandom", O_RDONLY | O_CLOEXEC);
        if (fd < 0) {
            log.error("xauthority", "urandom_open_failed", {{"errno", errno_text(errno)}});
            return false;
        }
        size_t off = 0;
        while (off < cookie_.size()) {
            ssize_t r = ::read(fd, cookie_.data() + off, cookie_.size() - off);
            if (r < 0) {
                if (errno == EINTR) {
                    continue;
                }
                log.error("xauthority", "urandom_read_failed", {{"errno", errno_text(errno)}});
                ::close(fd);
                return false;
            }
            if (r == 0) {
                log.error("xauthority", "urandom_eof");
                ::close(fd);
                return false;
            }
            off += static_cast<size_t>(r);
        }
        ::close(fd);
        return true;
    }

    bool write_auth(const std::string &path, uid_t uid, gid_t gid, Logger &log) const {
        int fd = ::open(path.c_str(), O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC | O_NOFOLLOW, 0600);
        if (fd < 0) {
            log.error("xauthority", "auth_open_failed", {{"path", path}, {"errno", errno_text(errno)}});
            return false;
        }
        FILE *fp = ::fdopen(fd, "w");
        if (!fp) {
            log.error("xauthority", "auth_fdopen_failed", {{"path", path}, {"errno", errno_text(errno)}});
            ::close(fd);
            return false;
        }

        char host[256];
        if (::gethostname(host, sizeof(host) - 1) != 0) {
            std::strncpy(host, "localhost", sizeof(host));
            host[sizeof(host) - 1] = '\0';
        } else {
            host[sizeof(host) - 1] = '\0';
        }
        std::string host_str(host);

        Xauth auth {};
        auth.family = FamilyLocal;
        auth.address_length = static_cast<unsigned short>(host_str.size());
        auth.address = host_str.empty() ? nullptr : const_cast<char *>(host_str.data());
        auth.number_length = static_cast<unsigned short>(display_number_.size());
        auth.number = display_number_.empty() ? nullptr : const_cast<char *>(display_number_.data());
        static const char kName[] = "MIT-MAGIC-COOKIE-1";
        auth.name_length = static_cast<unsigned short>(sizeof(kName) - 1);
        auth.name = const_cast<char *>(kName);
        auth.data_length = static_cast<unsigned short>(cookie_.size());
        auth.data = reinterpret_cast<char *>(const_cast<unsigned char *>(cookie_.data()));

        if (::fchown(fd, uid, gid) != 0) {
            log.error("xauthority", "auth_chown_failed", {{"path", path}, {"errno", errno_text(errno)}});
            ::fclose(fp);
            return false;
        }
        if (::fchmod(fd, 0600) != 0) {
            log.error("xauthority", "auth_chmod_failed", {{"path", path}, {"errno", errno_text(errno)}});
            ::fclose(fp);
            return false;
        }
        if (!XauWriteAuth(fp, &auth)) {
            log.error("xauthority", "auth_write_failed", {{"path", path}});
            ::fclose(fp);
            return false;
        }
        if (::fflush(fp) != 0) {
            log.error("xauthority", "auth_flush_failed", {{"path", path}, {"errno", errno_text(errno)}});
            ::fclose(fp);
            return false;
        }
        if (::fclose(fp) != 0) {
            log.error("xauthority", "auth_close_failed", {{"path", path}, {"errno", errno_text(errno)}});
            return false;
        }
        return true;
    }
};

struct SpawnResult {
    pid_t pid{-1};
    int exec_errno{0};
    bool spawned{false};
};

template <typename PrepareFn>
static SpawnResult spawn_process(const std::string &label, bool new_process_group, const std::vector<int> &keep_fds,
                                 PrepareFn &&prepare, Logger &log) {
    int pipefd[2];
    if (!make_pipe_cloexec(pipefd)) {
        log.error("process", "pipe_failed", {{"label", label}, {"errno", errno_text(errno)}});
        return {};
    }
    pid_t pid = ::fork();
    if (pid < 0) {
        log.error("process", "fork_failed", {{"label", label}, {"errno", errno_text(errno)}});
        ::close(pipefd[0]);
        ::close(pipefd[1]);
        return {};
    }
    if (pid == 0) {
        ::close(pipefd[0]);
        if (new_process_group && ::setpgid(0, 0) != 0) {
            int err = errno;
            (void)write_all(pipefd[1], reinterpret_cast<const char *>(&err), sizeof(err));
            _exit(127);
        }
        std::vector<int> keep = keep_fds;
        keep.push_back(pipefd[1]);
        close_fds_except(keep);
        int rc = prepare();
        if (rc == 0) {
            rc = EINVAL;
        }
        (void)write_all(pipefd[1], reinterpret_cast<const char *>(&rc), sizeof(rc));
        _exit(127);
    }

    ::close(pipefd[1]);
    int child_err = 0;
    ssize_t n = -1;
    while (true) {
        n = ::read(pipefd[0], &child_err, sizeof(child_err));
        if (n < 0 && errno == EINTR) {
            continue;
        }
        break;
    }
    ::close(pipefd[0]);
    if (n < 0) {
        int read_errno = errno;
        int status = 0;
        (void)::waitpid(pid, &status, 0);
        log.error("process", "exec_pipe_read_failed", {{"label", label}, {"errno", errno_text(read_errno)}});
        return {.pid = -1, .exec_errno = read_errno, .spawned = false};
    }
    if (n > 0) {
        int status = 0;
        (void)::waitpid(pid, &status, 0);
        log.error("process", "exec_failed", {{"label", label}, {"errno", errno_text(child_err)}});
        return {.pid = -1, .exec_errno = child_err, .spawned = false};
    }
    return {.pid = pid, .exec_errno = 0, .spawned = true};
}

class SignalWatcher {
public:
    bool init(Logger &log) {
        sigemptyset(&mask_);
        sigaddset(&mask_, SIGTERM);
        sigaddset(&mask_, SIGINT);
        sigaddset(&mask_, SIGHUP);
        sigaddset(&mask_, SIGCHLD);
        if (::sigprocmask(SIG_BLOCK, &mask_, nullptr) != 0) {
            log.error("signal", "sigprocmask_failed", {{"errno", errno_text(errno)}});
            return false;
        }
        int fd = ::signalfd(-1, &mask_, SFD_CLOEXEC | SFD_NONBLOCK);
        if (fd < 0) {
            log.error("signal", "signalfd_failed", {{"errno", errno_text(errno)}});
            return false;
        }
        fd_.reset(fd);
        return true;
    }

    int fd() const { return fd_.get(); }

    void drain(bool &terminate, bool &reload, bool &child, Logger &log) {
        struct signalfd_siginfo info {};
        while (true) {
            ssize_t n = ::read(fd_.get(), &info, sizeof(info));
            if (n < 0) {
                if (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR) {
                    return;
                }
                log.error("signal", "signalfd_read_failed", {{"errno", errno_text(errno)}});
                return;
            }
            if (n == 0) {
                return;
            }
            if (n != sizeof(info)) {
                return;
            }
            switch (info.ssi_signo) {
            case SIGTERM:
            case SIGINT:
                terminate = true;
                break;
            case SIGHUP:
                reload = true;
                break;
            case SIGCHLD:
                child = true;
                break;
            default:
                break;
            }
            std::memset(&info, 0, sizeof(info));
        }
    }

    bool wait_or_drain(int timeout_ms, bool &terminate, bool &reload, bool &child, Logger &log) {
        struct pollfd pfd { fd_.get(), POLLIN, 0 };
        int rc = ::poll(&pfd, 1, timeout_ms);
        if (rc < 0) {
            if (errno == EINTR) {
                return true;
            }
            log.error("signal", "poll_failed", {{"errno", errno_text(errno)}});
            return false;
        }
        if (rc == 0) {
            return true;
        }
        if (pfd.revents & POLLIN) {
            drain(terminate, reload, child, log);
        }
        return true;
    }

private:
    sigset_t mask_{};
    FdHandle fd_;
};

struct UserInfo {
    uid_t uid{};
    gid_t gid{};
    std::string username;
    std::string home;
    std::string shell;
};

enum class PamResultKind {
    AuthFailed,
    AccountFailed,
    OpenSessionFailed,
    Ok,
    Fatal
};

struct PamResult {
    PamResultKind kind{PamResultKind::Fatal};
    std::string error_text;
};

class PamSession {
public:
    explicit PamSession(Logger &log) : log_(&log) {}
    ~PamSession() { end(PAM_ABORT); }
    PamSession(const PamSession &) = delete;
    PamSession &operator=(const PamSession &) = delete;

    static int conversation(int num_msg, const pam_message **msg, pam_response **resp, void *appdata_ptr) {
        auto *state = static_cast<ConversationState *>(appdata_ptr);
        if (!state || !resp || num_msg <= 0) {
            return PAM_CONV_ERR;
        }
        pam_response *responses = static_cast<pam_response *>(std::calloc(static_cast<size_t>(num_msg), sizeof(pam_response)));
        if (!responses) {
            return PAM_BUF_ERR;
        }
        for (int i = 0; i < num_msg; ++i) {
            const pam_message *m = msg[i];
            if (!m) {
                std::free(responses);
                return PAM_CONV_ERR;
            }
            switch (m->msg_style) {
            case PAM_PROMPT_ECHO_OFF: {
                if (state->used_password) {
                    std::free(responses);
                    return PAM_CONV_ERR;
                }
                size_t len = state->password ? state->password->size() : 0;
                responses[i].resp = static_cast<char *>(std::malloc(len + 1));
                if (!responses[i].resp) {
                    std::free(responses);
                    return PAM_BUF_ERR;
                }
                if (len > 0) {
                    std::memcpy(responses[i].resp, state->password->data(), len);
                }
                responses[i].resp[len] = '\0';
                state->used_password = true;
                break;
            }
            case PAM_TEXT_INFO:
            case PAM_ERROR_MSG:
                responses[i].resp = nullptr;
                break;
            default:
                std::free(responses);
                return PAM_CONV_ERR;
            }
        }
        *resp = responses;
        return PAM_SUCCESS;
    }

    PamResult authenticate(const std::string &username, const std::vector<char> &password,
                           const std::string &display, const std::string &tty) {
        end(PAM_ABORT);
        ConversationState state;
        state.password = &password;
        pam_conv conv { &PamSession::conversation, &state };
        int rc = pam_start(kPamService, username.c_str(), &conv, handle_.out());
        if (rc != PAM_SUCCESS) {
            log_->error("pam", "pam_start_failed", {{"user", username}, {"pam", pam_err_name(rc)}});
            return {PamResultKind::Fatal, "pam_start_failed"};
        }

        std::string tty_item = tty;
        std::string display_item = display;
        (void)pam_set_item(handle_.get(), PAM_TTY, tty_item.c_str());
        (void)pam_set_item(handle_.get(), PAM_XDISPLAY, display_item.c_str());

        rc = pam_authenticate(handle_.get(), 0);
        if (rc != PAM_SUCCESS) {
            log_->error("pam", "authentication_failed", {
                {"user", username},
                {"display", display},
                {"pam", pam_err_name(rc)},
                {"detail", pam_strerror(handle_.get(), rc)}
            });
            end(rc);
            return {PamResultKind::AuthFailed, pam_strerror(handle_.get(), rc)};
        }
        rc = pam_acct_mgmt(handle_.get(), 0);
        if (rc != PAM_SUCCESS) {
            log_->error("pam", "account_failed", {
                {"user", username},
                {"display", display},
                {"pam", pam_err_name(rc)},
                {"detail", pam_strerror(handle_.get(), rc)}
            });
            end(rc);
            return {PamResultKind::AccountFailed, pam_strerror(handle_.get(), rc)};
        }
        rc = pam_setcred(handle_.get(), PAM_ESTABLISH_CRED);
        if (rc != PAM_SUCCESS) {
            log_->error("pam", "setcred_failed", {
                {"user", username},
                {"display", display},
                {"pam", pam_err_name(rc)},
                {"detail", pam_strerror(handle_.get(), rc)}
            });
            end(rc);
            return {PamResultKind::OpenSessionFailed, pam_strerror(handle_.get(), rc)};
        }
        cred_established_ = true;
        rc = pam_open_session(handle_.get(), 0);
        if (rc != PAM_SUCCESS) {
            log_->error("pam", "open_session_failed", {
                {"user", username},
                {"display", display},
                {"pam", pam_err_name(rc)},
                {"detail", pam_strerror(handle_.get(), rc)}
            });
            end(rc);
            return {PamResultKind::OpenSessionFailed, pam_strerror(handle_.get(), rc)};
        }
        session_open_ = true;
        log_->info("pam", "authentication_success", {{"user", username}, {"display", display}});
        return {PamResultKind::Ok, {}};
    }

    bool close_session(const std::string &username, const std::string &display) {
        bool ok = true;
        if (handle_) {
            if (session_open_) {
                int rc = pam_close_session(handle_.get(), 0);
                if (rc != PAM_SUCCESS) {
                    log_->error("pam", "close_session_failed", {
                        {"user", username},
                        {"display", display},
                        {"pam", pam_err_name(rc)},
                        {"detail", pam_strerror(handle_.get(), rc)}
                    });
                    ok = false;
                }
                session_open_ = false;
            }
            if (cred_established_) {
                int rc = pam_setcred(handle_.get(), PAM_DELETE_CRED);
                if (rc != PAM_SUCCESS) {
                    log_->error("pam", "delete_cred_failed", {
                        {"user", username},
                        {"display", display},
                        {"pam", pam_err_name(rc)},
                        {"detail", pam_strerror(handle_.get(), rc)}
                    });
                    ok = false;
                }
                cred_established_ = false;
            }
        }
        end(ok ? PAM_SUCCESS : PAM_ABORT);
        return ok;
    }

    char **envlist() {
        if (!handle_) {
            return nullptr;
        }
        return pam_getenvlist(handle_.get());
    }

    explicit operator bool() const { return static_cast<bool>(handle_); }

private:
    struct ConversationState {
        const std::vector<char> *password{};
        bool used_password{false};
    };

    Logger *log_{nullptr};
    PamHandle handle_;
    bool session_open_{false};
    bool cred_established_{false};

    void end(int status) {
        if (handle_) {
            handle_.reset(status);
        }
        session_open_ = false;
        cred_established_ = false;
    }

    static const char *pam_err_name(int rc) {
        switch (rc) {
        case PAM_SUCCESS: return "PAM_SUCCESS";
        case PAM_OPEN_ERR: return "PAM_OPEN_ERR";
        case PAM_SYMBOL_ERR: return "PAM_SYMBOL_ERR";
        case PAM_SERVICE_ERR: return "PAM_SERVICE_ERR";
        case PAM_SYSTEM_ERR: return "PAM_SYSTEM_ERR";
        case PAM_BUF_ERR: return "PAM_BUF_ERR";
        case PAM_PERM_DENIED: return "PAM_PERM_DENIED";
        case PAM_AUTH_ERR: return "PAM_AUTH_ERR";
        case PAM_CRED_INSUFFICIENT: return "PAM_CRED_INSUFFICIENT";
        case PAM_AUTHINFO_UNAVAIL: return "PAM_AUTHINFO_UNAVAIL";
        case PAM_USER_UNKNOWN: return "PAM_USER_UNKNOWN";
        case PAM_MAXTRIES: return "PAM_MAXTRIES";
        case PAM_ACCT_EXPIRED: return "PAM_ACCT_EXPIRED";
        case PAM_SESSION_ERR: return "PAM_SESSION_ERR";
        case PAM_CRED_ERR: return "PAM_CRED_ERR";
        case PAM_CRED_EXPIRED: return "PAM_CRED_EXPIRED";
        case PAM_CRED_UNAVAIL: return "PAM_CRED_UNAVAIL";
        case PAM_NEW_AUTHTOK_REQD: return "PAM_NEW_AUTHTOK_REQD";
        case PAM_ABORT: return "PAM_ABORT";
        default: return "PAM_UNKNOWN";
        }
    }
};

static std::optional<UserInfo> resolve_user(const std::string &username, Logger &log) {
    long bufsize = ::sysconf(_SC_GETPW_R_SIZE_MAX);
    if (bufsize < 16384) {
        bufsize = 16384;
    }
    std::vector<char> buf(static_cast<size_t>(bufsize));
    struct passwd pwd {};
    struct passwd *result = nullptr;
    int rc = ::getpwnam_r(username.c_str(), &pwd, buf.data(), buf.size(), &result);
    if (rc != 0 || !result) {
        log.error("session", "getpwnam_failed", {{"user", username}, {"errno", errno_text(rc != 0 ? rc : errno)}});
        return std::nullopt;
    }
    if (!pwd.pw_name || username != pwd.pw_name) {
        log.error("session", "username_mismatch", {{"user", username}});
        return std::nullopt;
    }
    if (!pwd.pw_dir || pwd.pw_dir[0] == '\0') {
        log.error("session", "home_missing", {{"user", username}});
        return std::nullopt;
    }
    if (!pwd.pw_shell || pwd.pw_shell[0] == '\0') {
        log.error("session", "shell_missing", {{"user", username}});
        return std::nullopt;
    }
    struct stat st {};
    if (::stat(pwd.pw_dir, &st) != 0 || !S_ISDIR(st.st_mode)) {
        log.error("session", "home_not_directory", {{"user", username}, {"home", pwd.pw_dir}});
        return std::nullopt;
    }
    std::vector<char> uid_buf(static_cast<size_t>(bufsize));
    struct passwd uid_pwd {};
    struct passwd *uid_result = nullptr;
    rc = ::getpwuid_r(pwd.pw_uid, &uid_pwd, uid_buf.data(), uid_buf.size(), &uid_result);
    if (rc != 0 || !uid_result || !uid_result->pw_name || std::string(uid_result->pw_name) != username) {
        log.error("session", "uid_lookup_mismatch", {{"user", username}});
        return std::nullopt;
    }
    UserInfo info;
    info.uid = pwd.pw_uid;
    info.gid = pwd.pw_gid;
    info.username = username;
    info.home = pwd.pw_dir;
    info.shell = pwd.pw_shell;
    return info;
}

static std::vector<std::string> build_session_env(const UserInfo &user, const std::string &display,
                                                  const std::string &xauth_path, char **pam_env) {
    std::vector<std::pair<std::string, std::string>> env;
    env.emplace_back("DISPLAY", display);
    env.emplace_back("XAUTHORITY", xauth_path);
    env.emplace_back("HOME", user.home);
    env.emplace_back("USER", user.username);
    env.emplace_back("LOGNAME", user.username);
    env.emplace_back("SHELL", user.shell);
    env.emplace_back("PATH", "/usr/local/bin:/usr/bin:/bin");

    auto protected_key = [](const std::string &key) {
        return key == "DISPLAY" || key == "XAUTHORITY" || key == "USER" || key == "LOGNAME" ||
               key == "HOME" || key == "SHELL";
    };

    for (char **p = pam_env; p && *p; ++p) {
        std::string entry = *p;
        auto pos = entry.find('=');
        if (pos == std::string::npos) {
            continue;
        }
        std::string key = entry.substr(0, pos);
        std::string value = entry.substr(pos + 1);
        if (protected_key(key)) {
            continue;
        }
        auto it = std::find_if(env.begin(), env.end(), [&](const auto &kv) { return kv.first == key; });
        if (it != env.end()) {
            it->second = value;
        } else {
            env.emplace_back(std::move(key), std::move(value));
        }
    }

    std::vector<std::string> out;
    out.reserve(env.size());
    for (auto &kv : env) {
        out.push_back(kv.first + "=" + kv.second);
    }
    return out;
}

class XServer {
public:
    XServer(const Options &opts, const RuntimeDir &runtime, XAuthority &auth, Logger &log)
        : opts_(opts), runtime_(runtime), auth_(auth), log_(&log) {}

    bool start() {
        if (!runtime_.ensure_display_lock_clear(*log_)) {
            return false;
        }
        if (!auth_.generate(*log_)) {
            log_->error("xorg", "xauthority_generation_failed");
            return false;
        }
        if (!auth_.write_root(runtime_, *log_)) {
            return false;
        }
        log_->info("xorg", "command_path", {{"path", opts_.xorg}});
        std::vector<std::string> argv_storage = {
            opts_.xorg,
            opts_.display,
            "vt" + std::to_string(opts_.vt),
            "-nolisten",
            "tcp",
            "-auth",
            runtime_.root_auth_path(),
        };
        std::vector<char *> argv;
        for (auto &s : argv_storage) {
            argv.push_back(s.data());
        }
        argv.push_back(nullptr);

        auto prepare = [&]() -> int {
            ::execve(opts_.xorg.c_str(), argv.data(), environ);
            return errno;
        };

        SpawnResult spawned = spawn_process("Xorg", true, {}, prepare, *log_);
        if (!spawned.spawned) {
            log_->error("xorg", "spawn_failed", {{"path", opts_.xorg}});
            return false;
        }
        xorg_pid_ = spawned.pid;
        log_->info("xorg", "spawned", {{"pid", std::to_string(xorg_pid_)}, {"display", opts_.display}});
        return true;
    }

    bool wait_ready(SignalWatcher &signals, bool &terminate, bool &reload) {
        const std::string socket_path = runtime_.display_socket_path();
        int attempts = 0;
        while (attempts < 80) {
            bool child = false;
            if (!signals.wait_or_drain(250, terminate, reload, child, *log_)) {
                return false;
            }
            if (terminate || reload) {
                return false;
            }
            if (is_exited()) {
                log_->error("xorg", "process_exited_early", {{"pid", std::to_string(xorg_pid_)}});
                return false;
            }
            if (!path_exists(socket_path)) {
                ++attempts;
                continue;
            }
            ::setenv("XAUTHORITY", runtime_.root_auth_path().c_str(), 1);
            DisplayHandle test(::XOpenDisplay(opts_.display.c_str()));
            if (test) {
                log_->info("xorg", "readiness_success", {{"display", opts_.display}});
                return true;
            }
            log_->warn("xorg", "xopen_display_failed", {{"display", opts_.display}, {"errno", errno_text(errno)}});
            ++attempts;
        }
        log_->error("xorg", "readiness_timeout", {{"display", opts_.display}});
        return false;
    }

    bool stop(Logger &log) {
        if (xorg_pid_ <= 0) {
            return true;
        }
        bool ok = true;
        if (::kill(-xorg_pid_, SIGTERM) != 0 && errno != ESRCH) {
            log.error("xorg", "terminate_failed", {{"pid", std::to_string(xorg_pid_)}, {"errno", errno_text(errno)}});
            ok = false;
        }
        int status = 0;
        for (int i = 0; i < 30; ++i) {
            pid_t rc = ::waitpid(xorg_pid_, &status, WNOHANG);
            if (rc == xorg_pid_) {
                log_exit("xorg", status, log);
                xorg_pid_ = -1;
                return ok;
            }
            if (rc < 0 && errno != EINTR) {
                break;
            }
            usleep(100000);
        }
        if (::kill(-xorg_pid_, SIGKILL) != 0 && errno != ESRCH) {
            log.error("xorg", "kill_failed", {{"pid", std::to_string(xorg_pid_)}, {"errno", errno_text(errno)}});
            ok = false;
        }
        pid_t rc = ::waitpid(xorg_pid_, &status, 0);
        if (rc == xorg_pid_) {
            log_exit("xorg", status, log);
        }
        xorg_pid_ = -1;
        return ok;
    }

    bool is_exited() {
        if (xorg_pid_ <= 0) {
            return true;
        }
        int status = 0;
        pid_t rc = ::waitpid(xorg_pid_, &status, WNOHANG);
        if (rc == xorg_pid_) {
            log_exit("xorg", status, *log_);
            xorg_pid_ = -1;
            return true;
        }
        return false;
    }

    pid_t pid() const { return xorg_pid_; }

private:
    Options opts_;
    const RuntimeDir &runtime_;
    XAuthority &auth_;
    Logger *log_;
    pid_t xorg_pid_{-1};

    static void log_exit(const char *component, int status, Logger &log) {
        if (WIFEXITED(status)) {
            log.info(component, "exit", {{"code", std::to_string(WEXITSTATUS(status))}});
        } else if (WIFSIGNALED(status)) {
            log.info(component, "signal_exit", {{"signal", std::to_string(WTERMSIG(status))}});
        } else {
            log.info(component, "exit_unknown");
        }
    }
};

enum class GreeterResultKind {
    Submit,
    Terminate,
    Reload,
    XorgLost
};

struct GreeterResult {
    GreeterResultKind kind{GreeterResultKind::XorgLost};
    std::string username;
    std::vector<char> password;
};

class Greeter {
public:
    Greeter(DisplayHandle display, const Options &opts, Logger &log)
        : display_(std::move(display)), opts_(opts), log_(&log) {}

    bool init() {
        if (!display_) {
            log_->error("greeter", "display_missing");
            return false;
        }
        screen_ = x_default_screen(display_.get());
        root_ = x_root_window(display_.get(), screen_);
        cmap_ = x_default_colormap(display_.get(), screen_);
        if (!load_colors() || !ensure_font_path() || !load_fonts() || !load_hostname() || !create_window() || !create_gc() || !create_text_context()) {
            return false;
        }
        ::XSelectInput(display_.get(), window_.get(), ExposureMask | KeyPressMask | FocusChangeMask | StructureNotifyMask);
        ::XStoreName(display_.get(), window_.get(), "esxdm");
        ::XMapRaised(display_.get(), window_.get());
        ::XSetInputFocus(display_.get(), window_.get(), RevertToParent, CurrentTime);
        ::XSync(display_.get(), False);
        grab_keyboard();
        redraw();
        log_->info("greeter", "display_start", {{"display", opts_.display}});
        return true;
    }

    void close() {
        if (display_) {
            if (window_.get() != 0) {
                ::XUngrabKeyboard(display_.get(), CurrentTime);
            }
            xft_draw_.reset();
            xft_font_.reset();
            release_xft_colors();
            window_.reset();
            gc_.reset();
            font_.reset();
            display_.reset();
        }
    }

    void abandon() {
        xft_draw_.release();
        xft_font_.release();
        xft_colors_loaded_ = false;
        window_.release();
        gc_.release();
        font_.release();
        display_.release();
    }

    void set_status(const std::string &text, bool error = false) {
        status_ = text;
        status_error_ = error;
        redraw();
    }

    void clear_status() {
        status_.clear();
        status_error_ = false;
        redraw();
    }

    void show_fatal() {
        status_ = "esxdm encountered a fatal error.\nCheck /var/log/esxdm.log.";
        status_error_ = true;
        redraw_fatal();
    }

    GreeterResult collect(int sigfd, pid_t xorg_pid, SignalWatcher &signals) {
        GreeterResult result;
        int xfd = x_connection_number(display_.get());
        while (true) {
            if (xorg_pid > 0) {
                int status = 0;
                pid_t rc = ::waitpid(xorg_pid, &status, WNOHANG);
                if (rc == xorg_pid) {
                    log_->error("xorg", "died_while_greeter_active");
                    result.kind = GreeterResultKind::XorgLost;
                    return result;
                }
            }
            struct pollfd pfds[2];
            pfds[0] = {xfd, POLLIN | POLLERR | POLLHUP, 0};
            pfds[1] = {sigfd, POLLIN, 0};
            int rc = ::poll(pfds, 2, -1);
            if (rc < 0) {
                if (errno == EINTR) {
                    continue;
                }
                log_->error("greeter", "poll_failed", {{"errno", errno_text(errno)}});
                result.kind = GreeterResultKind::XorgLost;
                return result;
            }
            bool terminate = false;
            bool reload = false;
            bool child = false;
            if (pfds[1].revents & POLLIN) {
                signals.drain(terminate, reload, child, *log_);
            }
            if (terminate) {
                result.kind = GreeterResultKind::Terminate;
                return result;
            }
            if (reload) {
                result.kind = GreeterResultKind::Reload;
                return result;
            }
            if (pfds[0].revents & (POLLERR | POLLHUP | POLLNVAL)) {
                result.kind = GreeterResultKind::XorgLost;
                return result;
            }
            if (pfds[0].revents & POLLIN) {
                while (::XPending(display_.get()) > 0) {
                    XEvent ev {};
                    ::XNextEvent(display_.get(), &ev);
                    switch (ev.type) {
                    case Expose:
                        redraw();
                        break;
                    case KeyPress:
                        if (handle_key(ev.xkey, result)) {
                            return result;
                        }
                        break;
                    default:
                        break;
                    }
                }
            }
        }
    }

private:
    enum class TextBackend {
        Core,
        Xft
    };

    DisplayHandle display_;
    Options opts_;
    Logger *log_;
    int screen_{0};
    Window root_{0};
    Colormap cmap_{0};
    WindowHandle window_;
    GCHandle gc_;
    FontHandle font_;
    XftFontHandle xft_font_;
    XftDrawHandle xft_draw_;
    XColor bg_{};
    XColor panel_{};
    XColor turquoise_{};
    XColor turquoise_dark_{};
    XColor fg_{};
    XColor muted_{};
    XColor error_{};
    std::string username_;
    std::vector<char> password_;
    enum class Field { Username, Password };
    Field active_{Field::Username};
    std::string status_;
    bool status_error_{false};
    std::string host_name_{"localhost"};
    std::string font_name_{"unselected"};
    TextBackend text_backend_{TextBackend::Core};
    XftColor xft_bg_{};
    XftColor xft_panel_{};
    XftColor xft_turquoise_{};
    XftColor xft_turquoise_dark_{};
    XftColor xft_fg_{};
    XftColor xft_muted_{};
    XftColor xft_error_{};
    bool xft_colors_loaded_{false};

    bool load_color(const char *name, XColor &color) {
        XColor exact {};
        if (!::XAllocNamedColor(display_.get(), cmap_, name, &color, &exact)) {
            log_->error("greeter", "color_alloc_failed", {{"name", name}});
            return false;
        }
        return true;
    }

    bool load_colors() {
        return load_color("#002B2F", bg_) &&
               load_color("#003F46", panel_) &&
               load_color("#30D5C8", turquoise_) &&
               load_color("#008C95", turquoise_dark_) &&
               load_color("#E8FFFF", fg_) &&
               load_color("#9BDAD5", muted_) &&
               load_color("#FFB0B0", error_);
    }

    bool load_fonts() {
        const char *core_candidates[] = {
            "-bitstream-dejavu sans-medium-r-normal--0-0-0-0-p-0-iso10646-1",
            "fixed",
        };
        bool core_loaded = false;
        for (const char *name : core_candidates) {
            XFontStruct *font = ::XLoadQueryFont(display_.get(), name);
            if (font) {
                font_.reset();
                font_ = FontHandle(display_.get(), font);
                font_name_ = name;
                core_loaded = true;
                break;
            }
        }

        const int fallback_h = font_.get() ? (font_.get()->ascent + font_.get()->descent)
                                           : std::max(18, static_cast<int>(std::min(x_display_width(display_.get(), screen_),
                                                                                     x_display_height(display_.get(), screen_)) / 36));
        const int target_px = std::max(16, (fallback_h * 151 + 50) / 100);
        const std::string px = std::to_string(target_px);
        const std::string xft_candidates[] = {
            "DefaultSans:pixelsize=" + px,
            "DejaVu Sans:pixelsize=" + px,
            "DefaultSans:size=" + px,
            "DejaVu Sans:size=" + px,
        };

        for (const std::string &name : xft_candidates) {
            XftPattern *pattern = ::XftNameParse(name.c_str());
            if (!pattern) {
                continue;
            }
            ::XftPatternAddBool(pattern, FC_ANTIALIAS, FcFalse);
            ::XftPatternAddBool(pattern, FC_HINTING, FcTrue);
            ::XftPatternAddInteger(pattern, FC_RGBA, FC_RGBA_NONE);
            XftFont *font = ::XftFontOpenPattern(display_.get(), pattern);
            if (font) {
                xft_font_.reset();
                xft_font_ = XftFontHandle(display_.get(), font);
                text_backend_ = TextBackend::Xft;
                font_name_ = name;
                log_->info("greeter", "font_selected", {
                    {"backend", "xft"},
                    {"name", font_name_},
                    {"pixelsize", px}
                });
                return true;
            }
            ::XftPatternDestroy(pattern);
        }

        if (core_loaded) {
            text_backend_ = TextBackend::Core;
            log_->info("greeter", "font_selected", {
                {"backend", "core"},
                {"name", font_name_}
            });
            return true;
        }

        log_->error("greeter", "font_load_failed", {{"family", "DefaultSans/DejaVu Sans"}});
        return false;
    }

    bool ensure_font_path() {
        int count = 0;
        char **paths = ::XGetFontPath(display_.get(), &count);
        std::vector<std::string> merged;
        merged.reserve(static_cast<size_t>(count) + 1);
        bool have_dejavu = false;
        for (int i = 0; i < count; ++i) {
            if (paths && paths[i]) {
                std::string path = paths[i];
                if (path == "/usr/share/fonts/dejavu") {
                    have_dejavu = true;
                }
                merged.push_back(std::move(path));
            }
        }
        if (!have_dejavu) {
            merged.insert(merged.begin(), "/usr/share/fonts/dejavu");
        }
        std::vector<char *> pathv;
        pathv.reserve(merged.size());
        for (auto &path : merged) {
            pathv.push_back(path.data());
        }
        if (!pathv.empty()) {
            ::XSetFontPath(display_.get(), pathv.data(), static_cast<int>(pathv.size()));
            log_->info("greeter", "font_path_set", {{"path", "/usr/share/fonts/dejavu"}});
        }
        if (paths) {
            ::XFreeFontPath(paths);
        }
        return true;
    }

    bool load_xft_colors(Visual *visual) {
        release_xft_colors();
        if (!alloc_xft_color(visual, "#002B2F", xft_bg_) ||
            !alloc_xft_color(visual, "#003F46", xft_panel_) ||
            !alloc_xft_color(visual, "#30D5C8", xft_turquoise_) ||
            !alloc_xft_color(visual, "#008C95", xft_turquoise_dark_) ||
            !alloc_xft_color(visual, "#E8FFFF", xft_fg_) ||
            !alloc_xft_color(visual, "#9BDAD5", xft_muted_) ||
            !alloc_xft_color(visual, "#FFB0B0", xft_error_)) {
            release_xft_colors();
            return false;
        }
        xft_colors_loaded_ = true;
        return true;
    }

    void release_xft_colors() {
        if (!xft_colors_loaded_ || !display_) {
            xft_colors_loaded_ = false;
            return;
        }
        Visual *visual = x_default_visual(display_.get(), screen_);
        XftColorFree(display_.get(), visual, cmap_, &xft_bg_);
        XftColorFree(display_.get(), visual, cmap_, &xft_panel_);
        XftColorFree(display_.get(), visual, cmap_, &xft_turquoise_);
        XftColorFree(display_.get(), visual, cmap_, &xft_turquoise_dark_);
        XftColorFree(display_.get(), visual, cmap_, &xft_fg_);
        XftColorFree(display_.get(), visual, cmap_, &xft_muted_);
        XftColorFree(display_.get(), visual, cmap_, &xft_error_);
        xft_colors_loaded_ = false;
    }

    bool alloc_xft_color(Visual *visual, const char *name, XftColor &color) {
        if (!::XftColorAllocName(display_.get(), visual, cmap_, name, &color)) {
            log_->error("greeter", "xft_color_alloc_failed", {{"name", name}});
            return false;
        }
        return true;
    }

    bool load_hostname() {
        char host[256];
        if (::gethostname(host, sizeof(host) - 1) != 0) {
            log_->warn("greeter", "hostname_lookup_failed", {{"errno", errno_text(errno)}});
            host_name_ = "localhost";
            return true;
        }
        host[sizeof(host) - 1] = '\0';
        host_name_ = host[0] ? host : "localhost";
        return true;
    }

    bool create_window() {
        unsigned int sw = x_display_width(display_.get(), screen_);
        unsigned int sh = x_display_height(display_.get(), screen_);
        unsigned int w = std::max<unsigned int>(1, sw);
        unsigned int h = std::max<unsigned int>(1, sh);
        int x = 0;
        int y = 0;
        unsigned long values_mask = CWBackPixel | CWBorderPixel;
        XSetWindowAttributes attrs {};
        attrs.background_pixel = turquoise_dark_.pixel;
        attrs.border_pixel = turquoise_dark_.pixel;
        Window win = ::XCreateWindow(display_.get(), root_, x, y, w, h, 1,
                                     x_default_depth(display_.get(), screen_),
                                     InputOutput, x_default_visual(display_.get(), screen_),
                                     values_mask, &attrs);
        if (!win) {
            log_->error("greeter", "window_create_failed");
            return false;
        }
        window_ = WindowHandle(display_.get(), win);
        return true;
    }

    bool create_gc() {
        XGCValues values {};
        values.foreground = fg_.pixel;
        values.background = turquoise_dark_.pixel;
        GC gc = ::XCreateGC(display_.get(), window_.get(), GCForeground | GCBackground, &values);
        if (!gc) {
            log_->error("greeter", "gc_create_failed");
            return false;
        }
        gc_ = GCHandle(display_.get(), gc);
        return true;
    }

    bool create_text_context() {
        if (text_backend_ != TextBackend::Xft) {
            return true;
        }
        Visual *visual = x_default_visual(display_.get(), screen_);
        xft_draw_ = XftDrawHandle(display_.get(), window_.get(), visual, cmap_);
        if (!xft_draw_) {
            log_->warn("greeter", "xft_draw_create_failed");
            if (font_.get()) {
                text_backend_ = TextBackend::Core;
                xft_font_.reset();
                return true;
            }
            return false;
        }
        if (!load_xft_colors(visual)) {
            log_->warn("greeter", "xft_color_alloc_failed");
            xft_draw_.reset();
            if (font_.get()) {
                text_backend_ = TextBackend::Core;
                xft_font_.reset();
                return true;
            }
            return false;
        }
        return true;
    }

    void grab_keyboard() {
        for (int i = 0; i < 20; ++i) {
            int rc = ::XGrabKeyboard(display_.get(), window_.get(), True, GrabModeAsync, GrabModeAsync, CurrentTime);
            if (rc == GrabSuccess) {
                ::XSetInputFocus(display_.get(), window_.get(), RevertToParent, CurrentTime);
                return;
            }
            usleep(100000);
        }
        log_->warn("greeter", "keyboard_grab_failed");
    }

    int text_ascent() const {
        return (text_backend_ == TextBackend::Xft && xft_font_.get()) ? xft_font_.get()->ascent : font_.get()->ascent;
    }

    int text_descent() const {
        return (text_backend_ == TextBackend::Xft && xft_font_.get()) ? xft_font_.get()->descent : font_.get()->descent;
    }

    int text_height() const {
        return text_ascent() + text_descent();
    }

    int text_width(std::string_view text) const {
        if (text.empty()) {
            return 0;
        }
        if (text_backend_ == TextBackend::Xft && xft_font_.get()) {
            XGlyphInfo ext {};
            ::XftTextExtentsUtf8(display_.get(), xft_font_.get(),
                                 reinterpret_cast<const FcChar8 *>(text.data()),
                                 static_cast<int>(text.size()), &ext);
            return ext.xOff;
        }
        return ::XTextWidth(font_.get(), text.data(), static_cast<int>(text.size()));
    }

    int shadow_dx() const {
        return std::max(2, text_height() / 14);
    }

    int shadow_dy() const {
        return std::max(2, text_height() / 14);
    }

    void draw_text(int x, int y, std::string_view text, unsigned long core_pixel, const XftColor *xft_color) {
        if (text.empty()) {
            return;
        }
        if (text_backend_ == TextBackend::Xft && xft_draw_.get() && xft_font_.get() && xft_color) {
            ::XftDrawStringUtf8(xft_draw_.get(), xft_color, xft_font_.get(), x, y,
                                reinterpret_cast<const FcChar8 *>(text.data()),
                                static_cast<int>(text.size()));
            return;
        }
        ::XSetForeground(display_.get(), gc_.get(), core_pixel);
        ::XDrawString(display_.get(), window_.get(), gc_.get(), x, y, text.data(), static_cast<int>(text.size()));
    }

    void draw_shadowed_text(int x, int y, std::string_view text, unsigned long core_pixel,
                            const XftColor *xft_color, unsigned long shadow_pixel, const XftColor *shadow_xft) {
        const int dx = shadow_dx();
        const int dy = shadow_dy();
        draw_text(x + dx, y + dy, text, shadow_pixel, shadow_xft);
        draw_text(x, y, text, core_pixel, xft_color);
    }

    void draw_common(bool fatal = false) {
        const int screen_w = x_display_width(display_.get(), screen_);
        const int screen_h = x_display_height(display_.get(), screen_);
        ::XSetForeground(display_.get(), gc_.get(), turquoise_dark_.pixel);
        ::XFillRectangle(display_.get(), window_.get(), gc_.get(), 0, 0,
                         static_cast<unsigned int>(screen_w), static_cast<unsigned int>(screen_h));

        const int w = screen_w;
        const int h = screen_h;
        const int font_h = text_height();
        const int panel_w = std::max(1, w * 82 / 100);
        const int panel_h = std::max(1, h * 82 / 100);
        const int panel_x = std::max(0, (w - panel_w) / 2);
        const int panel_y = std::max(0, (h - panel_h) / 2);
        const int login_label_w = text_width("Login:");
        const int password_label_w = text_width("Password:");
        const int pad_x = std::max(panel_w / 14, font_h * 2);
        const int pad_y = std::max(panel_h / 14, font_h * 2);
        const int label_col_w = std::max(login_label_w, password_label_w) + pad_x / 2;
        const int field_gap = std::max(12, panel_w / 60);
        int field_w = std::max(1, panel_w - 2 * pad_x - label_col_w - field_gap);
        const int line_gap = std::max(font_h * 2 + 12, panel_h / 8);
        const int inner_x = panel_x + pad_x;
        const int title_baseline = panel_y + pad_y + text_ascent();
        const int subtitle_baseline = title_baseline + font_h + std::max(8, pad_y / 6);
        const int separator_y = subtitle_baseline + font_h / 2 + std::max(8, pad_y / 8);
        const int form_start_y = separator_y + font_h + std::max(18, pad_y / 4);
        const int bottom_y = panel_y + panel_h - std::max(font_h, pad_y / 2);
        int status_lines = 0;
        if (!status_.empty()) {
            status_lines = 1;
            for (char c : status_) {
                if (c == '\n') {
                    ++status_lines;
                }
            }
        }
        const int status_line_h = font_h + 4;
        int status_y = panel_y + panel_h - pad_y - (status_lines > 0 ? status_lines * status_line_h : status_line_h);
        status_y = std::max(status_y, form_start_y + 2 * line_gap + std::max(16, pad_y / 4));

        ::XSetForeground(display_.get(), gc_.get(), turquoise_.pixel);
        const int outer_margin = std::max(1, std::min(w, h) / 40);
        ::XDrawRectangle(display_.get(), window_.get(), gc_.get(), outer_margin, outer_margin,
                         static_cast<unsigned int>(std::max(0, w - outer_margin * 2)),
                         static_cast<unsigned int>(std::max(0, h - outer_margin * 2)));

        ::XSetForeground(display_.get(), gc_.get(), panel_.pixel);
        ::XFillRectangle(display_.get(), window_.get(), gc_.get(), panel_x, panel_y,
                         static_cast<unsigned int>(panel_w), static_cast<unsigned int>(panel_h));

        ::XSetForeground(display_.get(), gc_.get(), turquoise_dark_.pixel);
        ::XDrawRectangle(display_.get(), window_.get(), gc_.get(), panel_x, panel_y,
                         static_cast<unsigned int>(panel_w), static_cast<unsigned int>(panel_h));
        ::XDrawLine(display_.get(), window_.get(), gc_.get(), panel_x + 1, separator_y,
                    panel_x + std::max(1, panel_w - 2), separator_y);

        const int title_x = panel_x + (panel_w - text_width("esxdm")) / 2;
        const int subtitle_x = panel_x + (panel_w - text_width("Minimal X Display Manager")) / 2;

        draw_shadowed_text(title_x, title_baseline, "esxdm", turquoise_.pixel, &xft_turquoise_, bg_.pixel, &xft_bg_);
        draw_shadowed_text(subtitle_x, subtitle_baseline, "Minimal X Display Manager", fg_.pixel, &xft_fg_, bg_.pixel, &xft_bg_);

        if (!fatal) {
            draw_field(inner_x, form_start_y, label_col_w, field_w, "Login:", username_, active_ == Field::Username, false);
            draw_field(inner_x, form_start_y + line_gap, label_col_w, field_w, "Password:", mask(password_), active_ == Field::Password, true);
            draw_button_hint(panel_x, panel_y, panel_w, form_start_y + 2 * line_gap + std::max(8, pad_y / 12));
            draw_status(panel_x, panel_y, panel_w, panel_h, status_y);
            int bottom_x = panel_x + (panel_w - text_width(host_name_)) / 2;
            draw_shadowed_text(bottom_x, bottom_y, host_name_, muted_.pixel, &xft_muted_, bg_.pixel, &xft_bg_);
        } else {
            int msg_y = panel_y + panel_h / 2;
            std::string_view fatal1 = "esxdm encountered a fatal error.";
            std::string_view fatal2 = "Check /var/log/esxdm.log.";
            int fatal1_x = panel_x + (panel_w - text_width(fatal1)) / 2;
            int fatal2_x = panel_x + (panel_w - text_width(fatal2)) / 2;
            draw_shadowed_text(fatal1_x, msg_y - 10, fatal1, error_.pixel, &xft_error_, bg_.pixel, &xft_bg_);
            draw_shadowed_text(fatal2_x, msg_y + text_ascent() + 6, fatal2, error_.pixel, &xft_error_, bg_.pixel, &xft_bg_);
        }
        ::XSync(display_.get(), False);
    }

    void draw() {
        draw_common(false);
    }

    void redraw() {
        draw();
    }

    void redraw_fatal() {
        draw_common(true);
    }

    std::string mask(const std::vector<char> &value) const {
        return std::string(value.size(), '*');
    }

    void draw_field(int x, int y, int label_width, int field_w, const char *label, const std::string &value, bool active, bool password) {
        const int field_x = x + label_width + 12;
        const int field_h = text_height() + 14;
        draw_shadowed_text(x, y, label, fg_.pixel, &xft_fg_, bg_.pixel, &xft_bg_);
        ::XSetForeground(display_.get(), gc_.get(), active ? turquoise_.pixel : muted_.pixel);
        ::XDrawRectangle(display_.get(), window_.get(), gc_.get(), field_x - 8, y - text_ascent() - 6,
                         field_w, field_h);
        std::string show = password ? std::string(value.size(), '*') : value;
        int text_y = y;
        draw_shadowed_text(field_x, text_y, show, active ? fg_.pixel : muted_.pixel,
                           active ? &xft_fg_ : &xft_muted_, bg_.pixel, &xft_bg_);
        if (active) {
            int cursor_x = field_x + text_width(show);
            ::XSetForeground(display_.get(), gc_.get(), turquoise_.pixel);
            ::XDrawLine(display_.get(), window_.get(), gc_.get(), cursor_x, text_y + 3, cursor_x + 10, text_y + 3);
        }
    }

    void draw_button_hint(int panel_x, [[maybe_unused]] int panel_y, int panel_w, int y) {
        const char *hint = "[ Press Enter ]";
        int hint_x = panel_x + (panel_w - text_width(hint)) / 2;
        draw_shadowed_text(hint_x, y, hint, turquoise_.pixel, &xft_turquoise_, bg_.pixel, &xft_bg_);
    }

    void draw_status(int panel_x, [[maybe_unused]] int panel_y, [[maybe_unused]] int panel_w, [[maybe_unused]] int panel_h, int y) {
        if (status_.empty()) {
            return;
        }
        int x = panel_x + 36;
        std::istringstream lines(status_);
        std::string line;
        int offset = 0;
        while (std::getline(lines, line)) {
            if (status_error_) {
                draw_shadowed_text(x, y + offset, line, error_.pixel, &xft_error_, bg_.pixel, &xft_bg_);
            } else {
                draw_shadowed_text(x, y + offset, line, muted_.pixel, &xft_muted_, bg_.pixel, &xft_bg_);
            }
            offset += text_height() + 4;
        }
    }

    bool handle_key(const XKeyEvent &ev, GreeterResult &result) {
        KeySym sym = NoSymbol;
        char buf[64];
        int len = ::XLookupString(const_cast<XKeyEvent *>(&ev), buf, sizeof(buf), &sym, nullptr);
        bool ctrl = (ev.state & ControlMask) != 0;
        if (sym == XK_Escape) {
            if (!password_.empty()) {
                password_.clear();
            } else {
                username_.clear();
            }
            redraw();
            return false;
        }
        if (ctrl && (sym == XK_u || sym == XK_U)) {
            clear_active();
            return false;
        }
        if (sym == XK_Tab) {
            active_ = (active_ == Field::Username) ? Field::Password : Field::Username;
            redraw();
            return false;
        }
        if (sym == XK_BackSpace) {
            erase_active();
            return false;
        }
        if (sym == XK_Return || sym == XK_KP_Enter) {
            if (active_ == Field::Username) {
                if (!username_.empty()) {
                    active_ = Field::Password;
                    redraw();
                }
                return false;
            }
            result.kind = GreeterResultKind::Submit;
            result.username = username_;
            result.password = password_;
            return true;
        }
        if (len > 0) {
            for (int i = 0; i < len; ++i) {
                unsigned char c = static_cast<unsigned char>(buf[i]);
                if (!std::isprint(c)) {
                    continue;
                }
                append_active(static_cast<char>(c));
            }
            redraw();
        }
        return false;
    }

    void clear_active() {
        if (active_ == Field::Username) {
            username_.clear();
        } else {
            password_.clear();
        }
        redraw();
    }

    void erase_active() {
        if (active_ == Field::Username) {
            if (!username_.empty()) {
                username_.pop_back();
            }
        } else {
            if (!password_.empty()) {
                password_.pop_back();
            }
        }
        redraw();
    }

    void append_active(char c) {
        if (active_ == Field::Username) {
            if (username_.size() < kMaxUsername) {
                username_.push_back(c);
            }
        } else {
            if (password_.size() < kMaxPassword) {
                password_.push_back(c);
            }
        }
    }
};

enum class SessionLaunchKind {
    Ok,
    UserError,
    RecoverableError,
    Terminate,
    Reload
};

struct SessionLaunchResult {
    SessionLaunchKind kind{SessionLaunchKind::RecoverableError};
    int retry_count{0};
    std::string status_message;
};

class SessionRunner {
public:
    SessionRunner(const Options &opts, const RuntimeDir &runtime, Logger &log)
        : opts_(opts), runtime_(runtime), log_(&log) {}

    SessionLaunchResult run(const UserInfo &user, PamSession &pam, SignalWatcher &signals,
                            bool &terminate, bool &reload, int &retry_count,
                            const XAuthority &display_auth) {
        bool child = false;
        std::string xsession = user.home + "/.xsession";
        std::string user_auth = runtime_.user_auth_path(user.uid);
        auto cleanup_session_artifacts = [&]() -> bool {
            bool ok = true;
            if (!pam.close_session(user.username, opts_.display)) {
                ok = false;
            }
            if (!runtime_.cleanup_user(user.uid, *log_)) {
                ok = false;
            }
            if (::unlink(user_auth.c_str()) != 0 && errno != ENOENT) {
                log_->warn("session", "user_xauthority_cleanup_failed", {{"path", user_auth}, {"errno", errno_text(errno)}});
                ok = false;
            }
            return ok;
        };
        auto fail = [&](SessionLaunchKind kind, std::string message) {
            return SessionLaunchResult{kind, retry_count, std::move(message)};
        };
        auto terminate_process_group = [&](pid_t pgid) {
            if (pgid <= 0) {
                return;
            }
            (void)::kill(-pgid, SIGTERM);
            for (int i = 0; i < 30; ++i) {
                if (::kill(-pgid, 0) != 0 && errno == ESRCH) {
                    return;
                }
                usleep(100000);
            }
            (void)::kill(-pgid, SIGKILL);
            for (int i = 0; i < 20; ++i) {
                if (::kill(-pgid, 0) != 0 && errno == ESRCH) {
                    return;
                }
                usleep(100000);
            }
        };
        enum class Mode { Xsession, Fallback };
        Mode mode = Mode::Fallback;
        if (path_exists(xsession)) {
            if (!is_regular_executable(xsession)) {
                log_->error("session", ".xsession_not_executable", {{"user", user.username}, {"path", xsession}});
                (void)cleanup_session_artifacts();
                return fail(SessionLaunchKind::UserError, ".xsession is not executable");
            }
            mode = Mode::Xsession;
        } else if (!opts_.fallback_session) {
            log_->error("session", ".xsession_missing", {{"user", user.username}, {"path", xsession}});
            log_->error("session", ".xsession_missing_no_fallback", {{"user", user.username}, {"path", xsession}});
            (void)cleanup_session_artifacts();
            return fail(SessionLaunchKind::UserError, "No .xsession found and fallback is disabled");
        } else {
            log_->info("session", ".xsession_missing", {{"user", user.username}, {"path", xsession}});
        }

        if (!runtime_.ensure_user_dir(user.uid, user.gid, *log_)) {
            (void)cleanup_session_artifacts();
            return fail(SessionLaunchKind::RecoverableError, "Could not prepare the user runtime directory");
        }
        if (!display_auth.write_user(runtime_, user.uid, user.gid, *log_)) {
            log_->error("session", "user_xauthority_failed", {{"user", user.username}});
            (void)cleanup_session_artifacts();
            return fail(SessionLaunchKind::RecoverableError, "Could not write session Xauthority");
        }

        char **pam_env = pam.envlist();
        std::vector<std::string> env_strings = build_session_env(user, opts_.display, runtime_.user_auth_path(user.uid), pam_env);
        if (pam_env) {
            for (char **p = pam_env; *p; ++p) {
                secure_zero(*p, std::strlen(*p));
                std::free(*p);
            }
            std::free(pam_env);
        }

        std::vector<std::string> argv_session = {xsession};
        std::vector<std::string> argv_xterm = {"/usr/bin/xterm", "-geometry", "80x24+10+10", "-ls"};
        std::vector<std::string> argv_twm = {"/usr/bin/twm"};

        auto make_envp = [&](const std::vector<std::string> &env) {
            std::vector<char *> out;
            out.reserve(env.size() + 1);
            for (const auto &s : env) {
                out.push_back(const_cast<char *>(s.c_str()));
            }
            out.push_back(nullptr);
            return out;
        };

        pid_t session_pid = -1;
        if (mode == Mode::Xsession) {
            auto env_copy = env_strings;
            auto argv_copy = argv_session;
            auto prepare = [&]() -> int {
                if (::initgroups(user.username.c_str(), user.gid) != 0) {
                    return errno;
                }
                if (::setgid(user.gid) != 0) {
                    return errno;
                }
                if (::setuid(user.uid) != 0) {
                    return errno;
                }
                if (::chdir(user.home.c_str()) != 0) {
                    return errno;
                }
                close_fds_except({0, 1, 2});
                std::vector<char *> envp = make_envp(env_copy);
                std::vector<char *> argvp;
                for (auto &s : argv_copy) {
                    argvp.push_back(s.data());
                }
                argvp.push_back(nullptr);
                ::execve(xsession.c_str(), argvp.data(), envp.data());
                return errno;
            };
            SpawnResult spawned = spawn_process("xsession", true, {}, prepare, *log_);
            if (!spawned.spawned) {
                (void)cleanup_session_artifacts();
                return fail(SessionLaunchKind::RecoverableError,
                            "Failed to start .xsession: " + errno_text(spawned.exec_errno));
            }
            session_pid = spawned.pid;
            log_->info("session", "user_session_pid", {{"pid", std::to_string(session_pid)}, {"user", user.username}});
        } else {
            auto env_copy = env_strings;
            auto xterm_path = argv_xterm.front();
            auto twm_path = argv_twm.front();

            auto spawn_twm = [&]() {
                auto twm_env = env_copy;
                auto twm_prepare = [&]() -> int {
                    std::vector<char *> envp = make_envp(twm_env);
                    std::vector<char *> argvp;
                    for (auto &s : argv_twm) {
                        argvp.push_back(s.data());
                    }
                    argvp.push_back(nullptr);
                    ::execve(twm_path.c_str(), argvp.data(), envp.data());
                    return errno;
                };
                SpawnResult twm_spawn = spawn_process("twm", false, {}, twm_prepare, *log_);
                if (!twm_spawn.spawned) {
                    log_->warn("session", "fallback_twm_spawn_failed", {{"path", twm_path}, {"errno", errno_text(twm_spawn.exec_errno)}});
                } else {
                    log_->info("session", "fallback_twm_pid", {{"pid", std::to_string(twm_spawn.pid)}});
                }
            };

            auto prepare = [&]() -> int {
                if (::initgroups(user.username.c_str(), user.gid) != 0) {
                    return errno;
                }
                if (::setgid(user.gid) != 0) {
                    return errno;
                }
                if (::setuid(user.uid) != 0) {
                    return errno;
                }
                if (::chdir(user.home.c_str()) != 0) {
                    return errno;
                }
                close_fds_except({0, 1, 2});
                spawn_twm();
                std::vector<char *> envp = make_envp(env_copy);
                std::vector<char *> argvp;
                for (auto &s : argv_xterm) {
                    argvp.push_back(s.data());
                }
                argvp.push_back(nullptr);
                ::execve(xterm_path.c_str(), argvp.data(), envp.data());
                return errno;
            };
            SpawnResult spawned = spawn_process("xterm", true, {}, prepare, *log_);
            if (!spawned.spawned) {
                (void)cleanup_session_artifacts();
                return fail(SessionLaunchKind::RecoverableError,
                            "Failed to start fallback session: " + errno_text(spawned.exec_errno));
            }
            session_pid = spawned.pid;
            log_->info("session", "user_session_pid", {{"pid", std::to_string(session_pid)}, {"user", user.username}});
        }
        int status = 0;
        while (true) {
            if (terminate || reload) {
                if (session_pid > 0) {
                    terminate_process_group(session_pid);
                    wait_for_exit(session_pid, status);
                }
                log_->info("session", "shutdown_requested", {{"user", user.username}});
                (void)cleanup_session_artifacts();
                return SessionLaunchResult{terminate ? SessionLaunchKind::Terminate : SessionLaunchKind::Reload, retry_count, {}};
            }
            if (session_pid > 0) {
                pid_t rc = ::waitpid(session_pid, &status, WNOHANG);
                if (rc == session_pid) {
                    break;
                }
                if (rc < 0 && errno != EINTR) {
                    log_->error("session", "waitpid_failed", {{"pid", std::to_string(session_pid)}, {"errno", errno_text(errno)}});
                    break;
                }
            }
            if (!signals.wait_or_drain(250, terminate, reload, child, *log_)) {
                break;
            }
        }

        log_session_exit(user.username, status);
        if (session_pid > 0) {
            terminate_process_group(session_pid);
        }
        if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
            if (!cleanup_session_artifacts()) {
                log_->warn("session", "cleanup_failure", {{"user", user.username}});
                return fail(SessionLaunchKind::RecoverableError, "Session cleanup failed");
            }
            return fail(SessionLaunchKind::Ok, {});
        }

        std::string exit_message;
        if (WIFEXITED(status)) {
            exit_message = "Session exited with code " + std::to_string(WEXITSTATUS(status));
        } else if (WIFSIGNALED(status)) {
            exit_message = "Session terminated by signal " + std::to_string(WTERMSIG(status));
        } else {
            exit_message = "Session ended unexpectedly";
        }

        if (!cleanup_session_artifacts()) {
            log_->warn("session", "cleanup_failure", {{"user", user.username}});
            return fail(SessionLaunchKind::RecoverableError, exit_message);
        }
        return fail(SessionLaunchKind::RecoverableError, exit_message);
    }

private:
    Options opts_;
    const RuntimeDir &runtime_;
    Logger *log_;

    static bool wait_for_exit(pid_t pid, int &status) {
        for (int i = 0; i < 30; ++i) {
            pid_t rc = ::waitpid(pid, &status, WNOHANG);
            if (rc == pid) {
                return true;
            }
            usleep(100000);
        }
        (void)::kill(-pid, SIGKILL);
        pid_t rc = ::waitpid(pid, &status, 0);
        return rc == pid;
    }

    void log_session_exit(const std::string &username, int status) {
        if (WIFEXITED(status)) {
            int code = WEXITSTATUS(status);
            if (code == 0) {
                log_->info("session", "user_session_exit", {{"user", username}, {"code", std::to_string(code)}});
            } else {
                log_->warn("session", "user_session_exit", {{"user", username}, {"code", std::to_string(code)}});
            }
        } else if (WIFSIGNALED(status)) {
            log_->warn("session", "user_session_signal", {{"user", username}, {"signal", std::to_string(WTERMSIG(status))}});
        } else {
            log_->warn("session", "user_session_exit_unknown", {{"user", username}});
        }
    }
};

static void print_usage(FILE *out) {
    std::fprintf(out,
                 "Usage: esxdm [options]\n"
                 "  --display DISPLAY          default :0\n"
                 "  --vt VT_NUMBER             default 7\n"
                 "  --xorg PATH                default /usr/bin/Xorg\n"
                 "  --log PATH                 default /var/log/esxdm.log\n"
                 "  --runtime-dir PATH         default /run/esxdm\n"
                 "  --retry-limit N            default 2, hard maximum 2\n"
                 "  --no-fallback-session      disable fallback xterm/twm session\n"
                 "  --help                     print usage and exit\n"
                 "  --version                  print version and exit\n");
}

static bool parse_args(int argc, char **argv, Options &opts) {
    for (int i = 1; i < argc; ++i) {
        std::string arg = argv[i];
        auto next = [&](std::string_view name) -> std::string {
            if (i + 1 >= argc) {
                throw std::runtime_error(std::string(name) + " requires an argument");
            }
            return argv[++i];
        };
        if (arg == "--help") {
            print_usage(stdout);
            std::exit(0);
        } else if (arg == "--version") {
            std::printf("%s\n", kVersion);
            std::exit(0);
        } else if (arg == "--display") {
            opts.display = next("--display");
            if (!parse_display_number(opts.display, opts.display_number)) {
                throw std::runtime_error("invalid --display value");
            }
        } else if (arg == "--vt") {
            std::string value = next("--vt");
            if (!parse_int(value, opts.vt) || opts.vt <= 0) {
                throw std::runtime_error("invalid --vt value");
            }
        } else if (arg == "--xorg") {
            opts.xorg = next("--xorg");
        } else if (arg == "--log") {
            opts.log_path = next("--log");
        } else if (arg == "--runtime-dir") {
            opts.runtime_dir = next("--runtime-dir");
        } else if (arg == "--retry-limit") {
            std::string value = next("--retry-limit");
            if (!parse_int(value, opts.retry_limit) || opts.retry_limit < 0 || opts.retry_limit > kMaxRetries) {
                throw std::runtime_error("invalid --retry-limit value");
            }
        } else if (arg == "--no-fallback-session") {
            opts.fallback_session = false;
        } else {
            throw std::runtime_error("unknown option: " + arg);
        }
    }
    return true;
}

class Daemon {
public:
    explicit Daemon(Options opts)
        : opts_(std::move(opts)),
          runtime_(opts_.runtime_dir, opts_.display_number),
          auth_(opts_.display, opts_.display_number),
          logger_(opts_.log_path),
          xserver_(opts_, runtime_, auth_, logger_),
          session_runner_(opts_, runtime_, logger_) {}

    int run() {
        logger_.info("daemon", "start", {
            {"display", opts_.display},
            {"vt", std::to_string(opts_.vt)},
            {"xorg", opts_.xorg},
            {"runtime_dir", opts_.runtime_dir},
            {"retry_limit", std::to_string(opts_.retry_limit)},
            {"fallback_session", opts_.fallback_session ? "true" : "false"}
        });
        SignalWatcher signals;
        if (!signals.init(logger_)) {
            return 1;
        }
        bool terminate = false;
        bool reload = false;
        int retry_count = 0;
        std::string pending_status;

        if (!runtime_.ensure_root(logger_)) {
            return 1;
        }

        while (!terminate) {
            if (!xserver_.start()) {
                if (!recoverable_failure("xorg_start_failed", retry_count)) {
                    return fatal_exit();
                }
                continue;
            }
            if (!xserver_.wait_ready(signals, terminate, reload)) {
                if (terminate) {
                    xserver_.stop(logger_);
                    return 0;
                }
                if (reload) {
                    xserver_.stop(logger_);
                    reload = false;
                    continue;
                }
                if (!recoverable_failure("xorg_readiness_failed", retry_count)) {
                    return fatal_exit();
                }
                xserver_.stop(logger_);
                continue;
            }

            DisplayHandle greeter_display(::XOpenDisplay(opts_.display.c_str()));
            if (!greeter_display) {
                logger_.error("daemon", "xopen_display_failed", {{"display", opts_.display}});
                if (!recoverable_failure("display_connect_failed", retry_count)) {
                    xserver_.stop(logger_);
                    return fatal_exit();
                }
                xserver_.stop(logger_);
                continue;
            }

            Greeter greeter(std::move(greeter_display), opts_, logger_);
            if (!greeter.init()) {
                if (!recoverable_failure("greeter_init_failed", retry_count)) {
                    xserver_.stop(logger_);
                    return fatal_exit();
                }
                greeter.close();
                xserver_.stop(logger_);
                continue;
            }
            if (!pending_status.empty()) {
                greeter.set_status(pending_status, true);
                pending_status.clear();
            }

            while (!terminate && !reload) {
                GreeterResult submission = greeter.collect(signals.fd(), xserver_.pid(), signals);
                if (submission.kind == GreeterResultKind::Terminate) {
                    terminate = true;
                    break;
                }
                if (submission.kind == GreeterResultKind::Reload) {
                    reload = true;
                    break;
                }
                if (submission.kind == GreeterResultKind::XorgLost) {
                    if (!recoverable_failure("xorg_lost", retry_count)) {
                        greeter.abandon();
                        return fatal_exit();
                    }
                    greeter.abandon();
                    xserver_.stop(logger_);
                    goto next_cycle;
                }
                if (submission.username.empty()) {
                    greeter.set_status("Login incorrect", true);
                    continue;
                }

                std::vector<char> password = submission.password;
                PamSession pam(logger_);
                PamResult pam_result = pam.authenticate(submission.username, password, opts_.display, "vt" + std::to_string(opts_.vt));
                secure_zero(password.data(), password.size());
                if (pam_result.kind == PamResultKind::AuthFailed || pam_result.kind == PamResultKind::AccountFailed) {
                    greeter.set_status("Login incorrect", true);
                    continue;
                }
                if (pam_result.kind == PamResultKind::OpenSessionFailed) {
                    greeter.set_status("Session startup failed: " + pam_result.error_text, true);
                    continue;
                }
                if (pam_result.kind == PamResultKind::Fatal) {
                    if (!recoverable_failure("pam_fatal", retry_count)) {
                        greeter.close();
                        xserver_.stop(logger_);
                        return fatal_exit();
                    }
                    greeter.close();
                    xserver_.stop(logger_);
                    goto next_cycle;
                }

                auto user = resolve_user(submission.username, logger_);
                if (!user) {
                    greeter.set_status("Login incorrect", true);
                    continue;
                }
                greeter.close();
                SessionLaunchResult session = session_runner_.run(*user, pam, signals, terminate, reload, retry_count, auth_);
                if (session.kind == SessionLaunchKind::Terminate) {
                    terminate = true;
                    runtime_.cleanup_root_auth(logger_);
                    xserver_.stop(logger_);
                    return 0;
                }
                if (session.kind == SessionLaunchKind::Reload) {
                    reload = true;
                    xserver_.stop(logger_);
                    break;
                }
                if (session.kind == SessionLaunchKind::RecoverableError) {
                    pending_status = session.status_message.empty() ? "Session startup failed" : session.status_message;
                    if (DisplayHandle status_display(::XOpenDisplay(opts_.display.c_str())); status_display) {
                        Greeter status_greeter(std::move(status_display), opts_, logger_);
                        if (status_greeter.init()) {
                            status_greeter.set_status(pending_status, true);
                            ::sleep(2);
                            status_greeter.close();
                        }
                    }
                    if (!recoverable_failure("session_launch_failed", retry_count)) {
                        xserver_.stop(logger_);
                        return fatal_exit();
                    }
                    xserver_.stop(logger_);
                    goto next_cycle;
                }
                if (session.kind == SessionLaunchKind::UserError) {
                    pending_status = session.status_message.empty() ? "Login rejected by session policy" : session.status_message;
                    if (DisplayHandle status_display(::XOpenDisplay(opts_.display.c_str())); status_display) {
                        Greeter status_greeter(std::move(status_display), opts_, logger_);
                        if (status_greeter.init()) {
                            status_greeter.set_status(pending_status, true);
                            ::sleep(2);
                            status_greeter.close();
                        }
                    }
                    xserver_.stop(logger_);
                    goto next_cycle;
                }
                if (session.kind == SessionLaunchKind::Ok) {
                    retry_count = 0;
                    xserver_.stop(logger_);
                    goto next_cycle;
                }
            }
            greeter.close();
            xserver_.stop(logger_);
        next_cycle:
            runtime_.cleanup_root_auth(logger_);
            if (reload) {
                reload = false;
            }
            if (terminate) {
                break;
            }
        }

        xserver_.stop(logger_);
        runtime_.cleanup_root_auth(logger_);
        return 0;
    }

private:
    Options opts_;
    RuntimeDir runtime_;
    XAuthority auth_;
    Logger logger_;
    XServer xserver_;
    SessionRunner session_runner_;

    bool recoverable_failure(const std::string &message, int &retry_count) {
        ++retry_count;
        logger_.warn("daemon", "retry_count", {{"count", std::to_string(retry_count)}});
        logger_.error("daemon", message, {{"retry_count", std::to_string(retry_count)}});
        return retry_count <= opts_.retry_limit;
    }

    int fatal_exit() {
        logger_.error("daemon", "fatal_exit", {{"retry_count", "exhausted"}});
        DisplayHandle fatal_display(::XOpenDisplay(opts_.display.c_str()));
        if (fatal_display) {
            Greeter fatal(std::move(fatal_display), opts_, logger_);
            if (fatal.init()) {
                fatal.show_fatal();
                ::sleep(2);
                fatal.close();
            }
        }
        runtime_.cleanup_root_auth(logger_);
        return 1;
    }
};

} // namespace

int main(int argc, char **argv) {
    try {
        Options opts;
        parse_args(argc, argv, opts);
        Daemon daemon(std::move(opts));
        return daemon.run();
    } catch (const std::exception &e) {
        std::fprintf(stderr, "%s\n", e.what());
        print_usage(stderr);
        return 2;
    }
}
