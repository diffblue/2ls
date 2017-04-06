include ../config.inc
CBMC ?= ../..

SRC = local_ssa.cpp \
      ssa_domain.cpp translate_union_member.cpp malloc_ssa.cpp ssa_pointed_objects.cpp \
      guard_map.cpp ssa_object.cpp assignments.cpp ssa_dereference.cpp \
      ssa_value_set.cpp address_canonizer.cpp simplify_ssa.cpp \
      ssa_build_goto_trace.cpp ssa_inliner.cpp ssa_unwinder.cpp \
      unwindable_local_ssa.cpp split_loopheads.cpp \
      ssa_heap_domain.cpp

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

CP_CXXFLAGS += $(SUMMARIZERFLAGS)

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: $(OBJ)

###############################################################################

