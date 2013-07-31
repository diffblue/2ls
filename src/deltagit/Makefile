include ../config.inc
CBMC ?= ../..

SRC = deltagit_main.cpp deltagit_parseoptions.cpp show_jobs.cpp \
      shell_escape.cpp do_git.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

LIBS =

CLEANFILES = deltagit$(EXEEXT)

all: deltagit$(EXEEXT)

###############################################################################

deltagit$(EXEEXT): $(OBJ)
	$(LINKBIN)

