/*******************************************************************\

Module: Equalities/Disequalities domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Equalities/Disequalities domain

#ifndef CPROVER_2LS_DOMAINS_EQUALITY_DOMAIN_H
#define CPROVER_2LS_DOMAINS_EQUALITY_DOMAIN_H

#include <set>

#include <util/std_expr.h>
#include <util/union_find.h>

#include "simple_domain.h"

class equality_domaint:public simple_domaint
{
public:
  typedef std::set<unsigned> index_sett;

  equality_domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    const var_specst &var_specs,
    const namespacet &ns):
    simple_domaint(_domain_number, _renaming_map, ns)
  {
    make_template(var_specs, ns);
  }

  struct template_row_exprt:simple_domaint::template_row_exprt
  {
    vart first;
    vart second;

    template_row_exprt(const vart &first, const vart &second):
      first(first), second(second) {}

    std::vector<exprt> get_row_exprs() override { return {}; };
    void output(std::ostream &out, const namespacet &ns) const override;
  };

  struct equ_valuet:simple_domaint::valuet
  {
    union_find<vart> equs;
    index_sett disequs;

    exprt get_row_expr(rowt row, const template_rowt &templ_row) const override;

    void set_equal(const vart &first, const vart &second)
    {
      equs.make_union(first, second);
    }

    void set_disequal(unsigned index) { disequs.insert(index); }

    equ_valuet *clone() override { return new equ_valuet(*this); }
  };

  std::unique_ptr<domaint::valuet> new_value() override
  {
    return std::unique_ptr<domaint::valuet>(new equ_valuet());
  }

  void initialize() override;

  void initialize_value(domaint::valuet &value) override;

  void init_value_solver_iteration(domaint::valuet &value) override;

  bool has_something_to_solve() override;

  bool edit_row(const rowt &row, valuet &inv, bool improved) override;

  void finalize_solver_iteration() override;

  exprt to_pre_constraints(const valuet &_value) override;

  void make_not_post_constraints(
    const valuet &_value,
    exprt::operandst &cond_exprs) override;

  exprt get_row_value_constraint(
    rowt row,
    const simple_domaint::valuet &value) override;

  bool handle_unsat(valuet &value, bool improved) override;
  exprt get_permanent_expr(valuet &value) override;

  void set_equal(unsigned index, equ_valuet &value);
  void set_disequal(unsigned index, equ_valuet &value);

  void output_value(
    std::ostream &out,
    const domaint::valuet &value,
    const namespacet &ns) const override;

  void project_on_vars(
    domaint::valuet &value,
    const var_sett &vars,
    exprt &result) override;

  void get_index_set(index_sett &indices);

protected:
  void make_template(
    const var_specst &var_specs,
    const namespacet &ns);

  bool adapt_types(exprt &v1, exprt &v2);
public:
  typedef std::set<unsigned> worklistt;
  worklistt::iterator e_it;
  worklistt todo_equs;
  worklistt todo_disequs;
  bool check_dis=false;
  bool unsatisfiable=false;
};

#endif // CPROVER_2LS_DOMAINS_EQUALITY_DOMAIN_H
