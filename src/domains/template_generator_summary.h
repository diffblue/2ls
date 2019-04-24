/*******************************************************************\

Module: Template Generator for Summaries

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator for Summaries

#ifndef CPROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_SUMMARY_H
#define CPROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_SUMMARY_H

#include "template_generator_base.h"

class template_generator_summaryt:public template_generator_baset
{
public:
  explicit template_generator_summaryt(
    optionst &_options,
    ssa_dbt &_ssa_db,
    ssa_local_unwindert &_ssa_local_unwinder):
    template_generator_baset(_options, _ssa_db, _ssa_local_unwinder)
  {
  }

  virtual void operator()(
    unsigned _domain_number,
    const local_SSAt &SSA,
    bool forward=true);

  virtual domaint::var_sett inout_vars();
  virtual domaint::var_sett loop_vars();
  virtual domaint::var_sett out_vars();

protected:
  virtual void collect_variables_inout(const local_SSAt &SSA, bool forward);
};

#endif
