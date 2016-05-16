include config.inc

SUBDIRS = summarizer ssa solver domains functions 

all: summarizer 
#deltagit

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

summarizer: domains ssa solver acdl
deltacheck: ssa solver functions html
deltagit: html


clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

cbmc-patch: $(CBMC_PATCH)
	PWD=`pwd`; cd $(CBMC); patch -p0 < $(PWD)/$(CBMC_PATCH)

