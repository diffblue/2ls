#ifndef CPROVER_PREDABS_DOMAIN_H
#define CPROVER_PREDABS_DOMAIN_H

#include "domain.h"

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <set>

class predabs_domaint : public domaint
{
public:
  typedef unsigned rowt;
  typedef exprt row_exprt; //predicate
  typedef constant_exprt row_valuet; //true/false

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

  predabs_domaint(replace_mapt &_renaming_map) :
    domaint(_renaming_map)
  {}

  // initialize value
  virtual void initialize(valuet &value);

  // value -> constraints
  exprt get_row_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const templ_valuet &value);
  exprt get_row_post_constraint(const rowt &row, const templ_valuet &value);

  exprt to_pre_constraints(const templ_valuet &value);
  void make_not_post_constraints(const templ_valuet &value,
			   exprt::operandst &cond_exprs);

  // set, get value
  row_valuet get_row_value(const rowt &row, const templ_valuet &value);
  void set_row_value(const rowt &row, const row_valuet &row_value, templ_valuet &value);

  // printing
  virtual void output_value(std::ostream &out, const valuet &value, const namespacet &ns) const;
  virtual void output_domain(std::ostream &out, const namespacet &ns) const;

  // projection  
  virtual void project_on_vars(valuet &value, const var_sett &vars, exprt &result);

  unsigned template_size();

  // generating templates
  void add_lin_inequ_template(const var_specst &var_specs,
			      const namespacet &ns);

protected:
  templatet templ;
  
};

#endif
