include ../config.inc
CBMC ?= ../..

SRC = call_graph.cpp summary.cpp index.cpp get_function.cpp path_util.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common


CP_CXXFLAGS += $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

