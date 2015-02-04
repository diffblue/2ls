include ../config.inc

SRC = storefront_main.cpp storefront_parse_options.cpp data.cpp \
      property_view.cpp file_view.cpp trace_view.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      ../html/html_escape$(OBJEXT) \
      ../html/syntax_highlighting$(OBJEXT) \
      ../html/logo$(OBJEXT)

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

INCLUDES= -I $(CBMC)/src

LIBS =

CLEANFILES = storefront$(EXEEXT)

all: storefront$(EXEEXT)

###############################################################################

storefront$(EXEEXT): $(OBJ)
	$(LINKBIN)

