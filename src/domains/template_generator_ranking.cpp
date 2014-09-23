/*******************************************************************\

Module: Template Generator for Ranking Functions

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator_ranking.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/mp_arith.h>

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: template_generator_rankingt::collect_variables_ranking

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_rankingt::collect_variables_ranking(local_SSAt &SSA,bool forward)
{
  collect_variables_loop(SSA,forward);
}

