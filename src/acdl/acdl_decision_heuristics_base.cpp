/*******************************************************************\

Module: ACDL Decision Heuristics

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "../ssa/local_ssa.h"
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

/*******************************************************************

 Function: acdl_solvert::order_decision_variables()

 Inputs:

 Outputs:

 Purpose: Order decision variables

 \*******************************************************************/

void acdl_decision_heuristics_baset::order_decision_variables(const local_SSAt &SSA)
{
  // [TODO] identify variables that has never been used in lhs 
  // do not make decisions on such variables
  
  // the following loop identifies variables with nondet as rhs
  for (local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin ();
      n_it != SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::equalitiest::const_iterator e_it =
        n_it->equalities.begin (); e_it != n_it->equalities.end (); e_it++)
    {
      exprt expr_rhs = to_equal_expr(*e_it).rhs();
      exprt expr_lhs = to_equal_expr(*e_it).lhs();
      //if(expr_rhs.id() == ID_constant) {
       std::string str("nondet");
       std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
       std::size_t found = rhs_str.find(str); 
       // push the nondet statement in rhs
       if(found != std::string::npos) {
        nondet_var.push_back(expr_lhs);
       }
    }
  }
}
  
