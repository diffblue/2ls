include ../config.inc
CBMC ?= ../..

SRC = deltarepo_main.cpp deltarepo_parseoptions.cpp show_jobs.cpp \
      update.cpp init.cpp deltarepo_config.cpp shell_escape.cpp \
      do_svn.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

LIBS =

CLEANFILES = deltarepo$(EXEEXT)

all: deltarepo$(EXEEXT)

###############################################################################

deltarepo$(EXEEXT): $(OBJ)
	$(LINKBIN)

