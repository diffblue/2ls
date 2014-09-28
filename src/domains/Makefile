include ../config.inc
CBMC ?= ../..

SRC = predicate.cpp fixed_point.cpp ssa_fixed_point.cpp \
  tpolyhedra_domain.cpp equality_domain.cpp domain.cpp \
  ssa_analyzer.cpp util.cpp \
  strategy_solver_base.cpp solver_enumeration.cpp \
  strategy_solver_enumeration.cpp strategy_solver_binsearch.cpp \
  template_generator_base.cpp template_generator_summary.cpp \
  template_generator_callingcontext.cpp \
  strategy_solver_binsearch2.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

