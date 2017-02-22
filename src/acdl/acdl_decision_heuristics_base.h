/*******************************************************************\

Module: ACDL Decision Heuristics Interface

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_BASE_H
#define CPROVER_2LS_ACDL_ACDL_DECISION_HEURISTICS_BASE_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_decision_heuristics_baset : public messaget
{
public:

  explicit acdl_decision_heuristics_baset(
    acdl_domaint &_domain)
    :
  domain(_domain)
  {
  }

  virtual ~acdl_decision_heuristics_baset()
  {
  }

  // override this
  virtual acdl_domaint::meet_irreduciblet operator()(
    const local_SSAt &SSA,
    const acdl_domaint::valuet &value)
  {
    assert(false);
  }

  acdl_domaint::statementt dec_statement;
  std::set<exprt> decision_variables;
  std::vector<std::pair<mp_integer, mp_integer> > decvar_val;
  std::vector<exprt> nondet_var;
  // stores all the meet irreducibles
  std::vector<acdl_domaint::meet_irreduciblet> decision_container;
  
  std::set<exprt> read_vars;
  std::set<exprt> assumption_vars;
  std::set<exprt> conditional_vars;
  exprt ssa_conjuncted;
  void get_dec_variables(const exprt &exp);
  void order_decision_variables(const local_SSAt &SSA);
  void initialize_decvar_val(std::pair<mp_integer, mp_integer> dec_val);

  /*void initialize_var_set(const acdl_domaint::varst &read_only_vars, const acdl_domaint::varst &assume_vars, const acdl_domaint::varst &cond_vars);*/

  void initialize_var_set(const std::set<exprt> &read_only_vars, const std::set<exprt> &assume_vars, const std::set<exprt> &cond_vars);


  void initialize_ssa(const exprt &ssa_conjunction);

protected:
  acdl_domaint &domain;
  bool phase;
};
#endif
