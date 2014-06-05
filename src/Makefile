SUBDIRS = summarizer ssa solver ai

all: summarizer 
#deltagit

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

summarizer: ai ssa solver functions html
deltacheck: ssa solver functions html
deltagit: html


clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

