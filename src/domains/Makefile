include ../config.inc
CBMC ?= ../..

SRC = predicate.cpp fixed_point.cpp ssa_fixed_point.cpp \
  template_domain.cpp equality_domain.cpp domain.cpp \
  ssa_analyzer.cpp \
  strategy_solver_base.cpp \
  strategy_solver_enumeration.cpp strategy_solver_binsearch.cpp 
# linrank_domain.cpp ranking_solver_enumeration.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

