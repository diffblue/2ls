SRC = tpolyhedra_domain.cpp equality_domain.cpp domain.cpp \
  predabs_domain.cpp heap_domain.cpp list_iterator.cpp \
  sympath_domain.cpp \ symbolic_path.cpp\
  ssa_analyzer.cpp util.cpp incremental_solver.cpp \
  strategy_solver_binsearch.cpp \
  strategy_solver_base.cpp \
  linrank_domain.cpp lexlinrank_domain.cpp \
  template_generator_base.cpp template_generator_summary.cpp \
  template_generator_callingcontext.cpp template_generator_ranking.cpp \
  strategy_solver_binsearch2.cpp strategy_solver_binsearch3.cpp \
  strategy_solver_sympath.cpp \
  simple_domain.cpp \
  strategy_solver_simple.cpp \
  product_domain.cpp \
  strategy_solver_product.cpp

include ../config.inc
include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CPROVER_DIR)/src -I ..

CLEANFILES = domains$(LIBEXT)

all: domains$(LIBEXT)

###############################################################################

domains$(LIBEXT): $(OBJ)
	$(LINKLIB)
