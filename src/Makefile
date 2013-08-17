SUBDIRS = deltacheck deltagit ssa

all: deltacheck deltagit

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

deltacheck: ssa

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

