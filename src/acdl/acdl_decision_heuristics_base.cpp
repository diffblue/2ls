/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_base.h"

#define DEBUG 1

/*******************************************************************

 Function: acdl_solvert::init_dec_var()

 Inputs:

 Outputs:

 Purpose: Initialize decision variables

 \*******************************************************************/

void acdl_decision_heuristics_baset::initialize_dec_variables(const exprt &exp)
{
  decision_variables.insert(exp); 
}
