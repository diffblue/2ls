#ifndef CPROVER_LINRANK_DOMAIN_H
#define CPROVER_LINRANK_DOMAIN_H

#include "domain.h"

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <set>
#include <vector>
#include <iostream>

class linrank_domaint : public domaint
{
public:
  typedef unsigned rowt;
  typedef exprt row_exprt; 
  typedef struct
  {
    std::vector<exprt> c;
    exprt d;
  } row_valuet;

  /*  typedef struct
  {
    std::vector<symbol_exprt> c;
    symbol_exprt d;
    } row_symb_valuet; */

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
  //typedef std::vector<std::pair<exprt::operandst,exprt::operandst> > pre_post_valuest;
  typedef std::vector<std::pair<exprt,exprt> > pre_post_valuest;


  linrank_domaint(replace_mapt &_renaming_map, 
                   templatet &_template) :
    domaint(_renaming_map),
    templ(_template) 
  {}

  // initialize value
  virtual void initialize(valuet &value);

  // value -> constraints
  exprt get_not_constraints(const templ_valuet &value,
			    exprt::operandst &cond_exprs,// identical to before 
			    pre_post_valuest &value_exprs); // (x, x')
  exprt get_row_symb_contraint(row_valuet &symb_values, // contains vars c and d
			       const rowt &row,
			       pre_post_valuest &values
			       );


  // set, get value
  row_valuet get_row_value(const rowt &row, const templ_valuet &value);
  void set_row_value(const rowt &row, const row_valuet &row_value, templ_valuet &value);

  // printing
  virtual void output_value(std::ostream &out, const valuet &value, const namespacet &ns) const;
  virtual void output_domain(std::ostream &out, const namespacet &ns) const;

  // projection  
  virtual void project_on_loops(const valuet &value, exprt &result);
  virtual void project_on_inout(const valuet &value, exprt &result);
  virtual void project_on_vars(const valuet &value, const var_sett &vars, exprt &result);

  unsigned template_size();

  // generating templates
  static void add_template(templatet &templ,
			      const var_specst &var_specs,
			      const namespacet &ns);

protected:
  templatet &templ;

  
};


#endif
