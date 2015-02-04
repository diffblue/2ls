include ../config.inc

SRC = storefront_main.cpp storefront_parseoptions.cpp

OBJ+= $(CBMC)/src/util/cmdline$(OBJEXT) \
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

