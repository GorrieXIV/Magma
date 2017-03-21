#$Id:: Makefile 1612 2008-12-16 03:53:07Z jbaa004                            $:

SHELL = /bin/sh

MODULES  = exceptional.dir prospector.dir
CLEAN    = $(MODULES:.dir=.clean)

.PHONY: all clean $(MODULES) $(CLEAN)

.SUFFIXES: .dir .clean

all: $(MODULES)

$(MODULES): 
	$(MAKE) -C $*

clean: $(CLEAN)

$(CLEAN):
	$(MAKE) -C $* clean

