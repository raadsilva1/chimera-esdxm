CXX ?= c++
PREFIX ?= /usr
BINDIR ?= $(PREFIX)/bin
DINITDIR ?= /usr/lib/dinit.d
PAMDIR ?= /usr/lib/pam.d
PKG_CONFIG ?= pkg-config

CXXFLAGS ?= -std=c++23 -O2 -pipe -Wall -Wextra -Wpedantic
XFT_CFLAGS ?= $(shell $(PKG_CONFIG) --cflags xft 2>/dev/null)
XFT_LIBS ?= $(shell $(PKG_CONFIG) --libs xft 2>/dev/null)
FONTCONFIG_LIBS ?= $(shell $(PKG_CONFIG) --libs fontconfig 2>/dev/null)
CXXFLAGS += $(XFT_CFLAGS)
LDLIBS ?= -lX11 -lXau -lpam $(XFT_LIBS) $(FONTCONFIG_LIBS)

all: esxdm

esxdm: esxdm.cpp
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

clean:
	rm -f esxdm

install: esxdm
	install -Dm755 esxdm "$(DESTDIR)$(BINDIR)/esxdm"
	install -d "$(DESTDIR)$(DINITDIR)"
	install -d "$(DESTDIR)$(PAMDIR)"
	printf '%s\n' \
		'# esxdm display manager' \
		'type = process' \
		'command = /usr/bin/esxdm --display :0 --vt 7' \
		'depends-on = turnstiled' \
		'waits-for = elogind' \
		'before = login.target' \
		'logfile = /var/log/esxdm.log' \
		'logfile-permissions = 0600' \
		'restart = on-failure' \
		'restart-delay = 1.0' \
		'restart-limit-count = 2' \
		'restart-limit-interval = 120' \
		'stop-timeout = 15' \
		> "$(DESTDIR)$(DINITDIR)/esxdm"
	printf '%s\n' \
		'auth     include system-login' \
		'account  include system-login' \
		'password include system-login' \
		'session  include system-login' \
		> "$(DESTDIR)$(PAMDIR)/esxdm"

uninstall:
	rm -f "$(DESTDIR)$(BINDIR)/esxdm"
	rm -f "$(DESTDIR)$(DINITDIR)/esxdm"
	rm -f "$(DESTDIR)$(PAMDIR)/esxdm"
