SRC = acdl_solver.cpp acdl_domain.cpp template_generator_acdl.cpp \
      acdl_decision_heuristics_base.cpp \
			acdl_decision_heuristics_rand.cpp \
			acdl_decision_heuristics_ordered.cpp \
			acdl_decision_heuristics_octagon.cpp \
      acdl_decision_heuristics_berkmin.cpp \
      acdl_decision_heuristics_largest_range.cpp \
			acdl_worklist_base.cpp \
	    acdl_worklist_ordered.cpp \
			acdl_worklist_forward_strategy.cpp \
			acdl_worklist_backward_strategy.cpp \
			acdl_analyze_conflict_base.cpp \
	    acdl_conflict_graph.cpp

include ../config.inc
include $(CBMC)/src/config.inc
include $(CBMC)/src/common
CBMC ?= ../..

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CBMC)/src -I ..

CLEANFILES = acdl$(LIBEXT)

all: acdl$(LIBEXT)

###############################################################################

acdl$(LIBEXT): $(OBJ)
	$(LINKLIB)
