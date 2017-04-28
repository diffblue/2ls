include ../config.inc
CBMC ?= ../..

SRC = predicate.cpp fixed_point.cpp ssa_fixed_point.cpp list_iterator.cpp \
  tpolyhedra_domain.cpp equality_domain.cpp heap_domain.cpp domain.cpp predabs_domain.cpp\
  heap_interval_domain.cpp \
  ssa_analyzer.cpp util.cpp incremental_solver.cpp \
  strategy_solver_base.cpp  \
  linrank_domain.cpp lexlinrank_domain.cpp\
  ranking_solver_enumeration.cpp lexlinrank_solver_enumeration.cpp \
  strategy_solver_enumeration.cpp strategy_solver_binsearch.cpp \
  template_generator_base.cpp template_generator_summary.cpp \
  template_generator_callingcontext.cpp template_generator_ranking.cpp \
  strategy_solver_binsearch2.cpp strategy_solver_binsearch3.cpp \
  strategy_solver_predabs.cpp strategy_solver_heap.cpp \
  strategy_solver_heap_interval.cpp
#solver_enumeration.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS += $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

