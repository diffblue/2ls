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

#include "domain.h"

class lexlinrank_domaint:public domaint
{
public:
  typedef unsigned rowt;
  typedef std::vector<std::pair<exprt, exprt> > pre_post_valuest;
  typedef pre_post_valuest row_exprt;
  typedef struct
  {
    std::vector<exprt> c;
  } row_value_elementt;

  typedef std::vector<row_value_elementt> row_valuet;

  class templ_valuet:public domaint::valuet, public std::vector<row_valuet>
  {
  };

  typedef struct
  {
    guardt pre_guard;
    guardt post_guard;
    row_exprt expr;
    kindt kind;
  } template_rowt;

  typedef std::vector<template_rowt> templatet;

  lexlinrank_domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    unsigned _max_elements, // lexicographic components
    unsigned _max_inner_iterations,
    const namespacet &_ns):
    domaint(_domain_number,  _renaming_map, _ns),
    refinement_level(0),
    max_elements(_max_elements),
    max_inner_iterations(_max_inner_iterations),
    number_inner_iterations(0)
    {
      inner_solver=incremental_solvert::allocate(_ns);
    }


  // initialize value
  virtual void initialize(valuet &value);

  const exprt initialize_solver(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  void solver_iter_init(domaint::valuet &rank);

  bool edit_row(const rowt &row, valuet &inv, bool improved);

  exprt to_pre_constraints(valuet &_value);

  void make_not_post_constraints(
    valuet &_value,
    exprt::operandst &cond_exprs);
  std::vector<exprt> get_required_smt_values(size_t row);
  void set_smt_values(std::vector<exprt> got_values, size_t row);
  virtual bool handle_unsat(valuet &value, bool improved);

  virtual bool refine();
  virtual void reset_refinements();

  // value -> constraints
  exprt get_not_constraints(
    const templ_valuet &value,
    exprt::operandst &cond_exprs, // identical to before
    std::vector<pre_post_valuest> &value_exprs); // (x, x')
  exprt get_row_symb_constraint(
    row_valuet &symb_values, // contains vars c and d
    const rowt &row,
    exprt &refinement_constraint);

  void add_element(const rowt &row, templ_valuet &value);

  // set, get value
  row_valuet get_row_value(const rowt &row, const templ_valuet &value);
  void set_row_value(
    const rowt &row,
    const row_valuet &row_value,
    templ_valuet &value);
  void set_row_value_to_true(const rowt &row, templ_valuet &value);

  // printing
  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const;
  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const;

  // projection
  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result);

  unsigned template_size() {return templ.size();}

  // generating templates
  void add_template(
    const var_specst &var_specs,
    const namespacet &ns);

  templatet templ;
  unsigned refinement_level;
  // the "inner" solver
  const unsigned max_elements; // lexicographic components
  const unsigned max_inner_iterations;
  incremental_solvert *inner_solver;
  unsigned number_inner_iterations;

protected:
  pre_post_valuest values;
  bool is_row_value_false(const row_valuet & row_value) const;
  bool is_row_value_true(const row_valuet & row_value) const;
  bool is_row_element_value_false(
    const row_value_elementt & row_value_element) const;
  bool is_row_element_value_true(
    const row_value_elementt & row_value_element) const;
public:
  // handles on values to retrieve from model
  std::vector<lexlinrank_domaint::pre_post_valuest> strategy_value_exprs;
  std::vector<unsigned> number_elements_per_row;
};

#endif // CPROVER_2LS_DOMAINS_LEXLINRANK_DOMAIN_H
