/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#ifndef SUMMARIZER_NONTERM_H
#define SUMMARIZER_NONTERM_H

#include <ssa/ssa_var_collector.h>

#include "summary_checker_base.h"

class summary_checker_nontermt : public summary_checker_baset
{
public:
  explicit summary_checker_nontermt(optionst &_options):
      summary_checker_baset(_options)
  {
  }

  virtual resultt operator()(const goto_modelt &);

  void check_properties(
    const ssa_dbt::functionst::const_iterator f_it);
  
protected:
  typedef struct loop_varst
  {
    loop_varst(exprt _loop_guard)
      : loop_guard(_loop_guard)
    {
    }
    exprt loop_guard;
    exprt::operandst loop_vars_eq;
  } loop_varst;

  typedef std::vector<loop_varst> var_collectort;
  typedef std::map<unsigned, var_collectort> loops_collectort;

  loops_collectort loop_map;
};

#endif /* SUMMARIZER_NONTERM_H */

