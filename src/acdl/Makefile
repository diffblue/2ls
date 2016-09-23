include ../config.inc
CBMC ?= ../..
#CBMC = ~/cbmc/trunk

SRC = acdl_solver.cpp acdl_domain.cpp template_generator_acdl.cpp \
      acdl_decision_heuristics_base.cpp acdl_decision_heuristics_rand.cpp \
			acdl_decision_heuristics_ordered.cpp acdl_decision_heuristics_octagon.cpp \
      acdl_decision_heuristics_berkmin.cpp acdl_worklist_base.cpp acdl_worklist_ordered.cpp \
      acdl_decision_heuristics_largest_range.cpp acdl_analyze_conflict_base.cpp \
	    acdl_conflict_graph.cpp acdl_worklist_forward_strategy.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS += $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

#all: heaven$(EXEEXT)
all: $(OBJ)

###############################################################################

heaven$(EXEEXT): $(OBJ)
	$(LINKBIN)
