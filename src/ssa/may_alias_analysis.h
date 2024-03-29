/*******************************************************************\

Module: May-alias analysis for a single function

Author: Viktor Malik, imalik@fit.vutbr.cz

\*******************************************************************/

/// \file
/// May-alias analysis for a single function

#ifndef CPROVER_2LS_SSA_MAY_ALIAS_ANALYSIS_H
#define CPROVER_2LS_SSA_MAY_ALIAS_ANALYSIS_H

#include <analyses/ai.h>
#include <util/union_find.h>
#include <util/threeval.h>
#include "ssa_value_set.h"

class may_alias_domaint:public ai_domain_baset
{
public:
  may_alias_domaint(): has_values(false) {}

  void transform(
    const irep_idt &,
    trace_ptrt trace_from,
    const irep_idt &,
    trace_ptrt trace_to,
    ai_baset &ai,
    const namespacet &ns) override;
  bool merge(
    const may_alias_domaint &other,
    trace_ptrt trace_from,
    trace_ptrt trace_to);

  void make_bottom() override
  {
    aliases.clear();
    has_values=tvt(false);
  }

  void make_top() override
  {
    aliases.clear();
    has_values=tvt(true);
  }

  void make_entry() override
  {
    make_top();
  }

  bool is_bottom() const override
  {
    return has_values.is_false();
  }

  bool is_top() const override
  {
    return has_values.is_true();
  }

  typedef union_find<irep_idt> aliasest;
  aliasest aliases;

protected:
  tvt has_values;

  void assign_lhs_aliases(
    const exprt &lhs,
    const std::set<irep_idt> &rhs_alias_set);
  void get_rhs_aliases(const exprt &rhs, std::set<irep_idt> &alias_set);

  static const exprt dereference(const exprt &expr, const namespacet &ns);
  static void members_to_symbols(exprt &expr, const namespacet &ns);
};

class may_alias_analysist:public ait<may_alias_domaint>
{
public:
  may_alias_analysist(
    const irep_idt &function_identifier,
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(function_identifier, goto_function, ns);
  }
protected:
  void initialize(
    const irep_idt &function_id,
    const goto_functionst::goto_functiont &goto_function) override;
};


#endif // CPROVER_2LS_SSA_MAY_ALIAS_ANALYSIS_H
