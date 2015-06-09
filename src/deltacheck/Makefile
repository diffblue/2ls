include ../config.inc
CBMC ?= ../..

SRC = deltacheck_main.cpp deltacheck_parse_options.cpp \
      rename.cpp ssa_fixed_point.cpp source_diff.cpp change_impact.cpp \
      html_report.cpp analyzer.cpp properties.cpp report_source_code.cpp \
      get_source.cpp statistics.cpp \
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
      $(CBMC)/src/util/util$(LIBEXT) \
      ../html/logo$(OBJEXT) \
      ../html/html_escape$(OBJEXT) \
      ../html/syntax_highlighting$(OBJEXT) \
      ../ssa/local_ssa$(OBJEXT) \
      ../ssa/malloc_ssa$(OBJEXT) \
      ../ssa/ssa_domain$(OBJEXT) \
      ../ssa/ssa_value_set$(OBJEXT) \
      ../ssa/assignments$(OBJEXT) \
      ../ssa/guard_map$(OBJEXT) \
      ../ssa/ssa_object$(OBJEXT) \
      ../ssa/address_canonizer$(OBJEXT) \
      ../ssa/ssa_dereference$(OBJEXT) \
      ../solver/predicate$(OBJEXT) \
      ../solver/solver$(OBJEXT) \
      ../solver/fixed_point$(OBJEXT) \
      ../functions/summary$(OBJEXT) \
      ../functions/path_util$(OBJEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src
# \
#  -I $(CUDD)/cudd -I $(CUDD)/obj -I $(CUDD)/mtr -I $(CUDD)/epd

LIBS =
#LIBS = $(CUDD)/cudd/libcudd.a $(CUDD)/mtr/libmtr.a \
#       $(CUDD)/st/libst.a $(CUDD)/epd/libepd.a $(CUDD)/util/libutil.a

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

# HTML Header

html_report$(OBJEXT): report_header.inc

report_header.inc: report_header.html
	../html/to_c_string.perl < report_header.html > $@

###############################################################################

deltacheck$(EXEEXT): $(OBJ)
	$(LINKBIN)

