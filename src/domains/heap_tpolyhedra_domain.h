/*******************************************************************\

Module: Combination of heap and template polyhedra abstract domains

Author: Viktor Malik

\*******************************************************************/
/// \file
/// Combination of heap and template polyhedra abstract domains

#ifndef CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_DOMAIN_H
#define CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_DOMAIN_H


#include "domain.h"
#include "tpolyhedra_domain.h"
#include "heap_domain.h"

class heap_tpolyhedra_domaint:public domaint
{
public:
  enum polyhedra_kindt
  {
    INTERVAL, ZONES, OCTAGONS
  };

  heap_domaint heap_domain;
  tpolyhedra_domaint polyhedra_domain;

  heap_tpolyhedra_domaint(
    unsigned int _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const local_SSAt &SSA,
    const polyhedra_kindt polyhedra_kind):
    domaint(_domain_number, _renaming_map, SSA.ns),
    heap_domain(_domain_number, _renaming_map, var_specs, SSA),
    polyhedra_domain(_domain_number, _renaming_map, ns)
  {
    if(polyhedra_kind==INTERVAL)
      polyhedra_domain.add_interval_template(var_specs, ns);
    else if(polyhedra_kind==ZONES)
    {
      polyhedra_domain.add_difference_template(var_specs, ns);
      polyhedra_domain.add_interval_template(var_specs, ns);
    }
  }

  class heap_tpolyhedra_valuet:public valuet
  {
  public:
    heap_domaint::heap_valuet heap_value;
    tpolyhedra_domaint::templ_valuet tpolyhedra_value;
  };

  virtual void initialize(valuet &value) override;

  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const override;

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const override;

  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result) override;

  // Restriction to symbolic paths
  void restrict_to_sympath(const symbolic_patht &sympath);
  void undo_restriction();
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths);
  void clear_aux_symbols();

  std::vector<exprt> get_required_smt_values(size_t row);
  void set_smt_values(std::vector<exprt> got_values, size_t row);

  // Value -> constraints
  exprt to_pre_constraints(valuet &_value);

  void make_not_post_constraints(
    valuet &_value,
    exprt::operandst &cond_exprs);

  bool edit_row(const rowt &row, valuet &inv, bool improved);
};

#endif // CPROVER_2LS_DOMAINS_HEAP_TPOLYHEDRA_DOMAIN_H
