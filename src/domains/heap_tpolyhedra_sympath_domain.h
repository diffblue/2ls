/*******************************************************************\

Module: Abstract domain for computing invariants in heap-tpolyhedra
        domain for different symbolic paths in program.

Author: Viktor Malik

\*******************************************************************/

/// \file
/// Abstract domain for computing invariants in heap-tpolyhedra domain for
///   different symbolic paths in program.

#ifndef CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_SYMPATH_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_SYMPATH_DOMAIN_H


#include "domain.h"
#include "heap_tpolyhedra_domain.h"

class heap_tpolyhedra_sympath_domaint:public domaint
{
public:
  heap_tpolyhedra_domaint heap_tpolyhedra_domain;

  heap_tpolyhedra_sympath_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA,
    const heap_tpolyhedra_domaint::polyhedra_kindt polyhedra_kind):
    domaint(_domain_number, _renaming_map, SSA.ns),
    heap_tpolyhedra_domain(
      _domain_number, _renaming_map, var_specs, SSA, polyhedra_kind)
  {
    exprt::operandst false_loop_guards;
    for(auto &g : SSA.loop_guards)
      false_loop_guards.push_back(not_exprt(g.first));
    no_loops_path=conjunction(false_loop_guards);
  }

  // Value is a map from expression (symbolic path) to an invariant in heap
  // tpolyhedra domain
  class heap_tpolyhedra_sympath_valuet:
    public valuet,
    public std::map<exprt, heap_tpolyhedra_domaint::heap_tpolyhedra_valuet>
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

  std::vector<exprt> get_required_smt_values(size_t row);
  void set_smt_values(std::vector<exprt> got_values, size_t row);

  // Value -> constraints
  exprt to_pre_constraints(valuet &_value);

  void make_not_post_constraints(
    valuet &_value,
    exprt::operandst &cond_exprs);

  bool edit_row(const rowt &row, valuet &inv, bool improved);

protected:
  // Special path containing conjunction negations of all loop-select guards
  // This must be stored explicitly since the solver is not able to explore this
  // path even though it can be feasible
  exprt no_loops_path;

  friend class strategy_solver_heap_tpolyhedra_sympatht;
};


#endif // CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_SYMPATH_DOMAIN_H
