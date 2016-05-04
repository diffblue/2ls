include ../config.inc
CBMC ?= ../..
#CBMC = ~/cbmc/trunk

SRC = acdl_solver.cpp acdl_domain.cpp template_generator_acdl.cpp \
      acdl_decision_heuristics.cpp \
      acdl_worklist_base.cpp acdl_worklist_ordered.cpp \
      acdl_conflict_analysis_base.cpp acdl_implication_graph.cpp acdl_graph_dominator.cpp

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
