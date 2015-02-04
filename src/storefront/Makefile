include ../config.inc

SRC = storefront_main.cpp storefront_parse_options.cpp data.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      ../html/html_escape$(OBJEXT) \
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

