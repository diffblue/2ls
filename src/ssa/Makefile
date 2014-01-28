include ../config.inc
CBMC ?= ../..

SRC = local_ssa.cpp ssa_domain.cpp guard_domain.cpp \
      guard_map.cpp ssa_object.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

