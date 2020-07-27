SRC = local_ssa.cpp ssa_var_collector.cpp \
      ssa_domain.cpp translate_union_member.cpp \
      malloc_ssa.cpp ssa_pointed_objects.cpp \
      guard_map.cpp ssa_object.cpp assignments.cpp ssa_dereference.cpp \
      ssa_value_set.cpp address_canonizer.cpp simplify_ssa.cpp \
      ssa_build_goto_trace.cpp ssa_inliner.cpp ssa_unwinder.cpp \
      unwindable_local_ssa.cpp ssa_db.cpp \
      ssa_pointed_objects.cpp  may_alias_analysis.cpp \
      dynobj_instance_analysis.cpp

include ../config.inc
include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CPROVER_DIR)/src -I ..

CLEANFILES = ssa$(LIBEXT)

all: ssa$(LIBEXT)

###############################################################################

ssa$(LIBEXT): $(OBJ)
	$(LINKLIB)
