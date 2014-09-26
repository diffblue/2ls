#ifndef CPROVER_TEMPLATE_DOMAIN_H
#define CPROVER_TEMPLATE_DOMAIN_H

#include "domain.h"

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <set>

class tpolyhedra_domaint : public domaint
{
public:
  typedef unsigned rowt;
  typedef exprt row_exprt; 
  typedef constant_exprt row_valuet; // "bound"

  class templ_valuet : public domaint::valuet, public std::vector<row_valuet> 
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

  tpolyhedra_domaint(replace_mapt &_renaming_map) :
    domaint(_renaming_map)
  {}

  // initialize value
  virtual void initialize(valuet &value);

  virtual void join(valuet &value1, const valuet &value2);

  // value -> constraints
  exprt get_row_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const templ_valuet &value);
  exprt get_row_post_constraint(const rowt &row, const templ_valuet &value);

  exprt to_pre_constraints(const templ_valuet &value);
  void make_not_post_constraints(const templ_valuet &value,
			   exprt::operandst &cond_exprs, 
			   exprt::operandst &value_exprs);

  // value -> symbolic bound constraints (for optimization)
  exprt to_symb_pre_constraints(const templ_valuet &value);
  exprt to_symb_pre_constraints(const templ_valuet &value,
				const std::set<rowt> &symb_rows);
  exprt to_symb_post_constraints();
  exprt get_row_symb_value_constraint(const rowt &row, 
				      const row_valuet &row_value);
  exprt get_row_symb_pre_constraint(const rowt &row, 
				      const row_valuet &row_value);
  exprt get_row_symb_post_constraint(const rowt &row);


  // set, get value
  row_valuet get_row_value(const rowt &row, const templ_valuet &value);
  void set_row_value(const rowt &row, const row_valuet &row_value, templ_valuet &value);

  // max, min, comparison
  row_valuet get_max_row_value(const rowt &row);
  row_valuet get_min_row_value(const rowt &row);
  row_valuet between(const row_valuet &lower, const row_valuet &upper);
  bool less_than(const row_valuet &v1, const row_valuet &v2);
  bool is_row_value_inf(const row_valuet & row_value) const;
  bool is_row_value_neginf(const row_valuet & row_value) const;

  // printing
  virtual void output_value(std::ostream &out, const valuet &value, const namespacet &ns) const;
  virtual void output_domain(std::ostream &out, const namespacet &ns) const;

  // projection  
  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result);

  unsigned template_size();

  // generating templates
  void add_interval_template(const var_specst &var_specs,
			      const namespacet &ns);
  void add_zone_template(const var_specst &var_specs,
				 const namespacet &ns);
  void add_octagon_template(const var_specst &var_specs,
				    const namespacet &ns);

  exprt get_row_symb_value(const rowt &row);

protected:
  friend class strategy_solver_binsearcht;

  templatet templ;
  
};

void extend_expr_types(exprt &expr);
constant_exprt simplify_const(const exprt &expr);
ieee_floatt simplify_const_float(const exprt &expr);
mp_integer simplify_const_int(const exprt &expr);



#endif
