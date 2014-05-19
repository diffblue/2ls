SUBDIRS = deltacheck deltagit ssa solver ai functions html

all: deltacheck deltagit

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

deltacheck: ssa solver ai functions html
deltagit: html

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

