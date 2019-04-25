/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

/// \file
/// Summarizer for Nontermination Bit-level analysis

#ifndef CPROVER_2LS_2LS_SUMMARY_CHECKER_NONTERM_H
#define CPROVER_2LS_2LS_SUMMARY_CHECKER_NONTERM_H

#include "summary_checker_base.h"

class summary_checker_nontermt:public summary_checker_baset
{
public:
  explicit summary_checker_nontermt(
    optionst &_options,
    const ssa_heap_analysist &heap_analysis):
    summary_checker_baset(_options, heap_analysis)
  {
  }

  virtual resultt operator()(const goto_modelt &);

  void check_properties(
    const ssa_dbt::functionst::const_iterator f_it);

  void check_properties_linear(
    const ssa_dbt::functionst::const_iterator f_it);

protected:
  summary_checker_baset::resultt check_nonterm_linear();
};

#endif // CPROVER_2LS_2LS_SUMMARY_CHECKER_NONTERM_H
