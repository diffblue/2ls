include ../config.inc
include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

SRC = 2ls_main.cpp 2ls_parse_options.cpp \
      2ls_languages.cpp \
      show.cpp summary_checker_base.cpp \
      summary_checker_ai.cpp summary_checker_bmc.cpp \
      summary_checker_kind.cpp summary_checker_nonterm.cpp \
      cover_goals_ext.cpp horn_encoding.cpp \
      preprocessing_util.cpp \
      instrument_goto.cpp dynamic_cfg.cpp \
      graphml_witness_ext.cpp

OBJ+= $(CPROVER_DIR)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CPROVER_DIR)/src/linking/linking$(LIBEXT) \
      $(CPROVER_DIR)/src/assembler/assembler$(LIBEXT) \
      $(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
      $(CPROVER_DIR)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CPROVER_DIR)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CPROVER_DIR)/src/analyses/analyses$(LIBEXT) \
      $(CPROVER_DIR)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/src/xmllang/xmllang$(LIBEXT) \
      $(CPROVER_DIR)/src/json/json$(LIBEXT) \
      $(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
      $(CPROVER_DIR)/src/util/util$(LIBEXT) \
      $(CPROVER_DIR)/src/goto-instrument/unwind$(OBJEXT) \
      $(CPROVER_DIR)/src/goto-instrument/unwindset$(OBJEXT) \
      ../domains/domains$(LIBEXT) \
      ../ssa/ssa$(LIBEXT) \
      ../solver/solver$(LIBEXT) \

CP_CXXFLAGS+= $(TWOLSFLAGS)

INCLUDES= -I $(CPROVER_DIR)/src -I ..

LIBS = 

CLEANFILES = 2ls$(EXEEXT) $(DELTA_OBJ)

all: 2ls$(EXEEXT)

ifneq ($(wildcard $(CPROVER_DIR)/src/cpp/Makefile),)
  OBJ += $(CPROVER_DIR)/src/cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CPROVER_DIR)/src/java/Makefile),)
  OBJ += $(CPROVER_DIR)/src/java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

###############################################################################

2ls$(EXEEXT): $(OBJ)
	$(LINKBIN)

