include ../config.inc
CBMC ?= ../..

SRC = main.cpp parseoptions.cpp summarization.cpp collation.cpp \
      cgraph_builder.cpp \
      modular_code_analysis.cpp \
      modular_fptr_analysis.cpp \
      modular_globals_analysis.cpp \
      xml_conversion.cpp \
      transformer.cpp \
      $(CBMC)/src/cbmc/xml_interface.cpp

OBJ+= $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT)

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util \
  -I $(CUDD)/cudd -I $(CUDD)/obj -I $(CUDD)/mtr -I $(CUDD)/epd

LIBS =

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

