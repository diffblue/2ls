include config.inc

DIRS = 2ls ssa domains solver acdl

all: 2ls.dir ssa.dir domains.dir solver.dir acdl.dir

###############################################################################

.PHONY: clean

ssa.dir: 
domains.dir: ssa.dir
acdl.dir: ssa.dir domains.dir
solver.dir: ssa.dir domains.dir
2ls.dir: ssa.dir domains.dir solver.dir acdl.dir

# building for a particular directory

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# cleaning

clean: $(patsubst %, %_clean, $(DIRS))

$(patsubst %, %_clean, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
