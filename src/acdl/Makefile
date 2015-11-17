include ../config.inc
CBMC ?= ../..
#CBMC = ~/cbmc/trunk

SRC = acdl_solver.cpp acdl_domain.cpp template_generator_acdl.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS += $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

#all: heaven$(EXEEXT)
all: $(OBJ)

###############################################################################

heaven$(EXEEXT): $(OBJ)
	$(LINKBIN)
