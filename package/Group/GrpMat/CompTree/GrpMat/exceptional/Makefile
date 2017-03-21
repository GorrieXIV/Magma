#$Id:: Makefile 531 2008-06-27 06:18:35Z jbaa004                             $:

SHELL = /bin/sh

MODULES  = suzuki.dir ree.dir large_ree.dir 
CLEAN    = $(MODULES:.dir=.clean)

.PHONY: all clean $(MODULES) $(CLEAN)

.SUFFIXES: .dir .clean

all: $(MODULES)

$(MODULES): 
	$(MAKE) -C $*

clean: $(CLEAN)

$(CLEAN):
	$(MAKE) -C $* clean
