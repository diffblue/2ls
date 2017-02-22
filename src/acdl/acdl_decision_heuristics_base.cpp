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

// #define DEBUG

/*******************************************************************

 Function: acdl_solvert::init_dec_var()

 Inputs:

 Outputs:

 Purpose: Initialize decision variables

 \*******************************************************************/

void acdl_decision_heuristics_baset::get_dec_variables(const exprt &exp)
{
  decision_variables.insert(exp);
}

/*******************************************************************

 Function: acdl_solvert::initial_val_range()

 Inputs:

 Outputs:

 Purpose: Initialize values for decision variables

 \*******************************************************************/

void acdl_decision_heuristics_baset::initialize_decvar_val
  (std::pair<mp_integer, mp_integer> val_pair)
{
  // this is a vector not a set
  // because we always want value
  // pair to be inserted at the end.
  // Set uses comparison operator
  // to sort the val_pair which we do
  // not want.

  // Note: The index of decision_variables set
  // and the decvar_val vector
  // are the same -- that is an entry in
  // decvar_val corresponds to the intial
  // value of the corresponding decision
  // variable at that index in decision_variables set
  decvar_val.push_back(val_pair);
}


/******************************************

 Function: acdl_solvert::initial_val_range()

 Inputs:

 Outputs:

 Purpose: Initialize Conjunction of SSA

 \*******************************************************************/

void acdl_decision_heuristics_baset::initialize_ssa(const exprt &ssa_conjunction)
{
  ssa_conjuncted = ssa_conjunction;
}

/******************************************

 Function: acdl_solvert::initial_val_range()

 Inputs:

 Outputs:

 Purpose: Initialize values for decision variables

 \*******************************************************************/

void acdl_decision_heuristics_baset::initialize_var_set(const std::set<exprt> &read_only_vars, const std::set<exprt> &assume_vars, const std::set<exprt> &cond_vars)
{
  read_vars.insert(read_only_vars.begin(), read_only_vars.end());
  assumption_vars.insert(assume_vars.begin(), assume_vars.end());
  conditional_vars.insert(cond_vars.begin(), cond_vars.end());


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
  for (local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin ();
       n_it!=SSA.nodes.end (); n_it++)
  {
    for (local_SSAt::nodet::equalitiest::const_iterator e_it=
           n_it->equalities.begin (); e_it!=n_it->equalities.end (); e_it++)
    {
      exprt expr_rhs=to_equal_expr(*e_it).rhs();
      exprt expr_lhs=to_equal_expr(*e_it).lhs();
      // if(expr_rhs.id()==ID_constant) {
      std::string str("nondet");
      std::string rhs_str=id2string(expr_rhs.get(ID_identifier));
      std::size_t found=rhs_str.find(str);
      // push the nondet statement in rhs
      if(found!=std::string::npos) {
        nondet_var.push_back(expr_lhs);
      }
    }
  }
}

