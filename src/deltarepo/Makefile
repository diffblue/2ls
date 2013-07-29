include ../config.inc
CBMC ?= ../..

SRC = deltarepo_main.cpp deltarepo_parseoptions.cpp show_jobs.cpp \
      update.cpp init.cpp

OBJ+= $(CBMC)/src/util/parseoptions$(OBJEXT) \
      $(CBMC)/src/util/cmdline$(OBJEXT) \
      $(CBMC)/src/util/signal_catcher$(OBJEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

LIBS =

CLEANFILES = deltarepo$(EXEEXT)

all: deltarepo$(EXEEXT)

###############################################################################

deltarepo$(EXEEXT): $(OBJ)
	$(LINKBIN)

