/*******************************************************************\

Module: Abstract domain for computing invariants in heap-interval
        domain for different symbolic paths in program.

Author: Viktor Malik

\*******************************************************************/

#ifndef CPROVER_2LS_DOMAINS_HEAP_INTERVAL_SYMPATH_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_INTERVAL_SYMPATH_DOMAIN_H


#include "domain.h"
#include "heap_interval_domain.h"

class heap_interval_sympath_domaint:public domaint
{
public:
  heap_interval_domaint heap_interval_domain;

  heap_interval_sympath_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA):
    domaint(_domain_number, _renaming_map, SSA.ns),
    heap_interval_domain(_domain_number, _renaming_map, var_specs, SSA.ns)
  {
    exprt::operandst false_loop_guards;
    for(auto &g : SSA.loop_guards)
      false_loop_guards.push_back(not_exprt(g));
    no_loops_path=conjunction(false_loop_guards);
  }

  // Value is a map from expression (symbolic path) to an invariant in heap
  // interval domain
  class heap_interval_sympath_valuet:
    public valuet,
    public std::map<exprt, heap_interval_domaint::heap_interval_valuet>
  {
  };

  void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result) override;

protected:
  // Special path containing conjunction negations of all loop-select guards
  // This must be stored explicitly since the solver is not able to explore this
  // path even though it can be feasible
  exprt no_loops_path;

  friend class strategy_solver_heap_interval_sympatht;
};


#endif // CPROVER_2LS_DOMAINS_HEAP_INTERVAL_SYMPATH_DOMAIN_H
