/*******************************************************************\

Module: Template Generator for Calling Contexts

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator for Calling Contexts

#ifndef CPROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_CALLINGCONTEXT_H
#define CPROVER_2LS_DOMAINS_TEMPLATE_GENERATOR_CALLINGCONTEXT_H

#include "template_generator_base.h"

class template_generator_callingcontextt:public template_generator_baset
{
public:
  explicit template_generator_callingcontextt(
    optionst &_options,
    ssa_dbt &_ssa_db,
    ssa_local_unwindert &_ssa_local_unwinder):
    template_generator_baset(_options, _ssa_db, _ssa_local_unwinder)
  {
  }

  virtual void operator()(
    unsigned _domain_number,
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    bool forward=true);

  virtual domaint::var_sett callingcontext_vars();

protected:
  virtual void collect_variables_callingcontext(
    const local_SSAt &SSA,
    local_SSAt::nodest::const_iterator n_it,
    local_SSAt::nodet::function_callst::const_iterator f_it,
    bool forward);
};

#endif
