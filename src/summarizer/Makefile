include ../config.inc

SRC = summarizer_main.cpp summarizer_parseoptions.cpp \
      show.cpp summary_checker.cpp  \
      summary_db.cpp summarizer.cpp summary.cpp ssa_db.cpp \
      array_abstraction.cpp

OBJ+= $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/assembler/assembler$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/analyses/analyses$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT) \


DELTA_OBJ+=\
      ../ssa/local_ssa$(OBJEXT) \
      ../ssa/malloc_ssa$(OBJEXT) \
      ../ssa/ssa_domain$(OBJEXT) \
      ../ssa/assignments$(OBJEXT) \
      ../ssa/guard_map$(OBJEXT) \
      ../ssa/ssa_object$(OBJEXT) \
      ../ssa/address_canonizer$(OBJEXT) \
      ../ssa/ssa_aliasing$(OBJEXT) \
      ../ssa/simplify_ssa$(OBJEXT) \
      ../ssa/ssa_build_goto_trace$(OBJEXT) \
      ../ssa/ssa_inliner$(OBJEXT)\
      ../ssa/ssa_unwinder$(OBJEXT)\
      ../functions/summary$(OBJEXT) \
      ../functions/get_function$(OBJEXT) \
      ../functions/path_util$(OBJEXT) \
      ../functions/index$(OBJEXT) \
      ../functions/index$(OBJEXT) \
      ../domains/fixed_point$(OBJEXT) \
      ../domains/ssa_fixed_point$(OBJEXT) \
      ../domains/tpolyhedra_domain$(OBJEXT) \
      ../domains/equality_domain$(OBJEXT) \
      ../domains/domain$(OBJEXT) \
      ../domains/util$(OBJEXT) \
      ../domains/strategy_solver_equality$(OBJEXT) \
      ../domains/strategy_solver_base$(OBJEXT) \
      ../domains/strategy_solver_enumeration$(OBJEXT) \
      ../domains/strategy_solver_binsearch$(OBJEXT) \
      ../domains/strategy_solver_binsearch2$(OBJEXT) \
      ../domains/template_generator_base$(OBJEXT) \
      ../domains/template_generator_summary$(OBJEXT) \
      ../domains/template_generator_callingcontext$(OBJEXT) \
      ../domains/ssa_analyzer$(OBJEXT) \
      ../domains/predicate$(OBJEXT) \
      ../domains/template_generator_ranking$(OBJEXT) \
      ../domains/ranking_solver_enumeration$(OBJEXT) \
      ../domains/linrank_domain$(OBJEXT) \
      ../domains/lexlinrank_solver_enumeration$(OBJEXT) \
      ../domains/lexlinrank_domain$(OBJEXT)

OBJ+=$(DELTA_OBJ)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src
# \
#  -I $(CUDD)/cudd -I $(CUDD)/obj -I $(CUDD)/mtr -I $(CUDD)/epd

LIBS =
#LIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/mtr/libmtr.a \
#       $(CUDD)/st/libst.a $(CUDD)/epd/libepd.a $(CUDD)/util/libutil.a

CP_CXXFLAGS +=-g

# $(CUDD)/obj/libobj.a 

CLEANFILES = summarizer$(EXEEXT) $(DELTA_OBJ)

all: summarizer$(EXEEXT)

ifneq ($(wildcard $(CBMC)/src/cpp/Makefile),)
  OBJ += $(CBMC)/src/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMC)/src/java/Makefile),)
  OBJ += $(CBMC)/src/java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

###############################################################################

summarizer$(EXEEXT): $(OBJ)
	$(LINKBIN)

