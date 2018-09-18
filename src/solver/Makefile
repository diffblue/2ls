SRC = summarizer_base.cpp  summarizer_bw.cpp	\
      summarizer_bw_term.cpp	summarizer_fw_contexts.cpp \
      summarizer_fw.cpp  summarizer_fw_term.cpp  \
      summarizer_rec_fw.cpp \
      summary.cpp  summary_db.cpp

include ../config.inc
include $(CBMC)/src/config.inc
include $(CBMC)/src/common
CBMC ?= ../..

CP_CXXFLAGS += $(TWOLSFLAGS)

INCLUDES= -I $(CBMC)/src -I ..

CLEANFILES = solver$(LIBEXT)

all: solver$(LIBEXT)

###############################################################################

solver$(LIBEXT): $(OBJ)
	$(LINKLIB)
