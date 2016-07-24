include config.inc

DIRS = 2ls ssa domains

all: 2ls.dir ssa.dir domains.dir

###############################################################################

.PHONY: clean

ssa.dir: 
domains.dir: ssa.dir
2ls.dir: ssa.dir domains.dir

# building for a particular directory

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# cleaning

clean: $(patsubst %, %_clean, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
