include ../config.inc
include $(CBMC)/src/config.inc
include $(CBMC)/src/common

SRC = 2ls_main.cpp 2ls_parse_options.cpp \
      2ls_languages.cpp \
      show.cpp summary_checker_base.cpp \
      summary_checker_ai.cpp summary_checker_bmc.cpp \
      summary_checker_kind.cpp \
      summary_checker_acdl.cpp \
      cover_goals_ext.cpp horn_encoding.cpp \
      preprocessing_util.cpp \
      instrument_goto.cpp dynamic_cfg.cpp \
      graphml_witness_ext.cpp

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
      $(CBMC)/src/json/json$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/goto-instrument/unwind$(OBJEXT) \
      ../domains/domains$(LIBEXT) \
      ../ssa/ssa$(LIBEXT) \
      ../acdl/acdl$(LIBEXT) \
      ../solver/solver$(LIBEXT) \

CP_CXXFLAGS+= $(TWOLSFLAGS)

INCLUDES= -I $(CBMC)/src -I ..

LIBS = 

CLEANFILES = 2ls$(EXEEXT) $(DELTA_OBJ)

all: 2ls$(EXEEXT)

ifneq ($(wildcard $(CBMC)/src/cpp/Makefile),)
  OBJ += $(CBMC)/src/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMC)/src/java/Makefile),)
  OBJ += $(CBMC)/src/java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

###############################################################################

2ls$(EXEEXT): $(OBJ)
	$(LINKBIN)

