include ../config.inc
CBMC ?= ../..

SRC = deltacheck_main.cpp deltacheck_parseoptions.cpp index.cpp \
      get_function.cpp function_ssa.cpp predicate.cpp \
      ssa_domain.cpp ssa_data_flow.cpp html_escape.cpp \
      html_report.cpp logo.cpp one_program_check.cpp \
      solver.cpp show.cpp delta_check.cpp report_assertions.cpp \
      extract_source.cpp statistics.cpp \
      $(CBMC)/src/cbmc/xml_interface.cpp

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
      $(CBMC)/src/util/util$(LIBEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src \
  -I $(CUDD)/cudd -I $(CUDD)/obj -I $(CUDD)/mtr -I $(CUDD)/epd

LIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/mtr/libmtr.a \
       $(CUDD)/st/libst.a $(CUDD)/epd/libepd.a $(CUDD)/util/libutil.a

# $(CUDD)/obj/libobj.a 

CLEANFILES = deltacheck$(EXEEXT)

all: deltacheck$(EXEEXT)

ifneq ($(wildcard $(CBMC)/src/cpp/Makefile),)
  OBJ += $(CBMC)/src/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMC)/src/java/Makefile),)
  OBJ += $(CBMC)/src/java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

ifneq ($(wildcard $(CBMC)/src/specc/Makefile),)
  OBJ += $(CBMC)/src/specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard $(CBMC)/src/php/Makefile),)
  OBJ += $(CBMC)/src/php/php$(LIBEXT)
  CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

deltacheck$(EXEEXT): $(OBJ)
	$(LINKBIN)

