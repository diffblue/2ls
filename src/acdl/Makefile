include ../config.inc
CBMC ?= ../..
#CBMC = ~/cbmc/trunk

SRC = acdl_solver.cpp acdl_domain.cpp template_generator_acdl.cpp \
      acdl_decision_heuristics_cond.cpp \
      acdl_worklist_base.cpp acdl_worklist_ordered.cpp acdl_clause_learning_base.cpp 

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
