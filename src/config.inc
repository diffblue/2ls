CPROVER_DIR = ../../lib/cbmc

# Variables you may want to override

# Enable warnings
CXXFLAGS += -Wall -Werror -Wno-long-long -Wno-sign-compare -Wno-parentheses -Wno-c++20-compat -Wno-strict-aliasing -pedantic

# Select optimisation or debug
#CXXFLAGS += -O2
#CXXFLAGS += -O0 -g

#static compilation
#LINKFLAGS += -static-libgcc -static-libstdc++

#2LS switches
TWOLS_FLAGS = 
