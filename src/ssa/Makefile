SRC = local_ssa.cpp ssa_var_collector.cpp \
      ssa_domain.cpp translate_union_member.cpp \
      malloc_ssa.cpp ssa_pointed_objects.cpp ssa_heap_domain.cpp \
      guard_map.cpp ssa_object.cpp assignments.cpp ssa_dereference.cpp \
      ssa_value_set.cpp address_canonizer.cpp simplify_ssa.cpp \
      ssa_build_goto_trace.cpp ssa_inliner.cpp ssa_unwinder.cpp \
      unwindable_local_ssa.cpp ssa_db.cpp \
      ssa_pointed_objects.cpp ssa_heap_domain.cpp may_alias_analysis.cpp

include ../config.inc
include $(CBMC)/src/config.inc
include $(CBMC)/src/common
CBMC ?= ../..

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CBMC)/src -I ..

CLEANFILES = ssa$(LIBEXT)

all: ssa$(LIBEXT)

###############################################################################

ssa$(LIBEXT): $(OBJ)
	$(LINKLIB)
