include ../config.inc
CBMC ?= ../..

SRC = local_ssa.cpp ssa_domain.cpp malloc_ssa.cpp \
      guard_map.cpp ssa_object.cpp assignments.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

