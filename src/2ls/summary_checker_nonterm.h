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

  void check_properties_linear(
    const ssa_dbt::functionst::const_iterator f_it);
  
protected:
  typedef struct loop_varst
  {
    source_locationt source_location;
    exprt::operandst guards;
    exprt::operandst vars;
    exprt::operandst loop_exits;
  } loop_varst;

  typedef std::map<unsigned, loop_varst> loops_collectort;

  loops_collectort loop_map;
  bool second_check_finished;

  summary_checker_baset::resultt check_nonterm_linear();
};

#endif /* SUMMARIZER_NONTERM_H */

