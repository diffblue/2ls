/*******************************************************************\

Module: Lexicographic linear ranking function domain

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Lexicographic linear ranking function domain

#ifndef CPROVER_2LS_DOMAINS_LEXLINRANK_DOMAIN_H
#define CPROVER_2LS_DOMAINS_LEXLINRANK_DOMAIN_H

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <domains/incremental_solver.h>
#include <util/ieee_float.h>
#include <set>
#include <vector>

#include "simple_domain.h"

class lexlinrank_domaint:public simple_domaint
{
public:
  struct template_row_exprt:simple_domaint::template_row_exprt
  {
    struct pre_post_valuet
    {
      exprt pre;
      exprt post;

      pre_post_valuet(const exprt &pre, const exprt &post):
        pre(pre), post(post) {}
    };

    std::vector<pre_post_valuet> pre_post_values;
    rowt row;

    std::vector<exprt> get_row_exprs() override;
    void output(std::ostream &out, const namespacet &ns) const override;
  };

  struct row_value_elementt
  {
    std::vector<exprt> c;

    void set_to_true()
    {
      c.clear();
      c.push_back(true_exprt());
    }
    void clear()
    {
      c.clear();
      c.push_back(false_exprt());
    }
    bool is_true() const { return c[0].get(ID_value)==ID_true; }
    bool is_false() const { return c[0].get(ID_value)==ID_false; }
  };

  struct row_valuet:std::vector<row_value_elementt>
  {
    void add_element()
    {
      push_back(row_value_elementt());
      for(auto &elem : *this)
        elem.clear();
    }
    void set_to_true()
    {
      clear();
      push_back(row_value_elementt());
      at(0).set_to_true();
    }
    bool is_true() const { return at(0).is_true(); }
    bool is_false() const { return at(0).is_false(); }
  };

  struct templ_valuet:simple_domaint::valuet, std::vector<row_valuet>
  {
    exprt get_row_expr(rowt row, const template_rowt &templ_row) const override
    {
      return true_exprt();
    }

    templ_valuet *clone() override { return new templ_valuet(*this); }
  };

  std::unique_ptr<domaint::valuet> new_value() override
  {
    return std::unique_ptr<domaint::valuet>(new templ_valuet());
  }

  lexlinrank_domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    unsigned _max_elements, // lexicographic components
    unsigned _max_inner_iterations,
    const namespacet &_ns,
    message_handlert &_message_handler):
    simple_domaint(_domain_number, _renaming_map, _ns),
    refinement_level(0),
    max_elements(_max_elements),
    max_inner_iterations(_max_inner_iterations),
    number_inner_iterations(0),
    message_handler(_message_handler)
  {
    inner_solver=incremental_solvert::allocate(_ns, _message_handler);
  }


  // initialize value
  void initialize_value(domaint::valuet &value) override;

  void initialize() override;

  void init_value_solver_iteration(domaint::valuet &rank) override;

  bool edit_row(const rowt &row, valuet &inv, bool improved) override;

  exprt to_pre_constraints(const valuet &_value) override;

  void make_not_post_constraints(
    const valuet &_value,
    exprt::operandst &cond_exprs) override;

  bool handle_unsat(valuet &value, bool improved) override;

  bool refine() override;
  void reset_refinements() override;

  // value -> constraints
  exprt get_row_symb_constraint(
    row_valuet &symb_values, // contains vars c and d
    const rowt &row,
    exprt &refinement_constraint);

  // printing
  void output_value(
    std::ostream &out,
    const domaint::valuet &value,
    const namespacet &ns) const override;

  // projection
  void project_on_vars(domaint::valuet &value,
                       const var_sett &vars,
                       exprt &result,
                       bool ignore_top) override;

  // generating templates
  void add_template(
    const var_specst &var_specs,
    const namespacet &ns);

  unsigned refinement_level;
  // the "inner" solver
  const unsigned max_elements; // lexicographic components
  const unsigned max_inner_iterations;
  incremental_solvert *inner_solver;
  unsigned number_inner_iterations;
  message_handlert &message_handler;

  std::vector<unsigned> number_elements_per_row;
};

#endif // CPROVER_2LS_DOMAINS_LEXLINRANK_DOMAIN_H
