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

#include "product_domain.h"
#include <ssa/local_ssa.h>

class heap_tpolyhedra_sympath_domaint:public domaint
{
public:
  product_domaint *heap_tpolyhedra_domain;

  heap_tpolyhedra_sympath_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const local_SSAt &SSA,
    product_domaint *heap_tpolyhedra_domain):
    domaint(_domain_number, _renaming_map, SSA.ns),
    heap_tpolyhedra_domain(heap_tpolyhedra_domain)
  {
    exprt::operandst false_loop_guards;
    for(auto &g : SSA.loop_guards)
      false_loop_guards.push_back(not_exprt(g.first));
    no_loops_path=conjunction(false_loop_guards);
  }

  ~heap_tpolyhedra_sympath_domaint() override { delete heap_tpolyhedra_domain; }

  // Value is a map from expression (symbolic path) to an invariant in heap
  // tpolyhedra domain
  class heap_tpolyhedra_sympath_valuet:
    public valuet,
    public std::map<exprt, product_domaint::valuet *>
  {
  public:
    explicit heap_tpolyhedra_sympath_valuet(
      product_domaint::valuet *inner_value_template):
      inner_value_template(inner_value_template) {}

    ~heap_tpolyhedra_sympath_valuet() override
    {
      for(auto &val : *this)
        delete val.second;
      delete inner_value_template;
    }

    heap_tpolyhedra_sympath_valuet *clone() override
    {
      auto new_value=new heap_tpolyhedra_sympath_valuet(inner_value_template);
      for(auto &val : *this)
        new_value->emplace(val.first, val.second->clone());
      return new_value;
    }

    // A template of the inner heap-tpolyhedra value that will be used to
    // create new values.
    product_domaint::valuet *inner_value_template;
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

  // These do not need to be implemented since there is no domain above this
  // one that would use it.
  void restrict_to_sympath(const symbolic_patht &sympath) override {}
  void eliminate_sympaths(
    const std::vector<symbolic_patht> &sympaths) override {}
  void undo_sympath_restriction() override {}
  void remove_all_sympath_restrictions() override {}

protected:
  // Special path containing conjunction negations of all loop-select guards
  // This must be stored explicitly since the solver is not able to explore this
  // path even though it can be feasible
  exprt no_loops_path;

  friend class strategy_solver_heap_tpolyhedra_sympatht;
};


#endif // CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_SYMPATH_DOMAIN_H
