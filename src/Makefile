SUBDIRS = summarizer ssa solver domains functions 

all: summarizer 
#deltagit

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

summarizer: domains ssa solver 
deltacheck: ssa solver functions html
deltagit: html
summarizer: ssa solver functions domains


clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

