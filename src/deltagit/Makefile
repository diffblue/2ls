include ../config.inc
CBMC ?= ../..

SRC = deltagit_main.cpp deltagit_parse_options.cpp show_jobs.cpp \
      shell_escape.cpp git_log.cpp git_branch.cpp job_status.cpp do_job.cpp \
      deltagit_config.cpp revisions_report.cpp init.cpp reset.cpp \
      reanalyse.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/json/json$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      ../html/html_escape$(OBJEXT) \
      ../html/logo$(OBJEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

LIBS =

CLEANFILES = deltagit$(EXEEXT)

all: deltagit$(EXEEXT)

revisions_report$(OBJEXT): revisions_report_header.inc

revisions_report_header.inc: revisions_report_header.html
	../html/to_c_string.perl < revisions_report_header.html > $@

###############################################################################

deltagit$(EXEEXT): $(OBJ)
	$(LINKBIN)

