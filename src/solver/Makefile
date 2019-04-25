SRC = summarizer_base.cpp  summarizer_bw.cpp	\
      summarizer_bw_term.cpp	summarizer_fw_contexts.cpp \
      summarizer_fw.cpp  summarizer_fw_term.cpp  \
      summary.cpp  summary_db.cpp

include ../config.inc
include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CPROVER_DIR)/src -I ..

CLEANFILES = solver$(LIBEXT)

all: solver$(LIBEXT)

###############################################################################

solver$(LIBEXT): $(OBJ)
	$(LINKLIB)
