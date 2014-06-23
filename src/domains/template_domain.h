#ifndef CPROVER_TEMPLATE_DOMAIN_H
#define CPROVER_TEMPLATE_DOMAIN_H

#include "domain.h"

#include <util/std_expr.h>

class template_domaint : public domaint
{
public:
  typedef unsigned rowt;
  typedef exprt row_exprt; 
  typedef std::vector<row_exprt> row_exprst; 
  typedef constant_exprt row_valuet; // "bound"
  typedef std::vector<exprt> var_guardst; 

  class templ_valuet : public domaint::valuet, public std::vector<row_valuet> 
  {
  };

  typedef struct 
  {
    guardst pre_guards;
    guardst post_guards;
    row_exprst rows;
    kindst kinds;

    unsigned size() { return rows.size(); } 
  } templatet;

 template_domaint(templatet &_template) :
  templ(_template) 
 {}

  virtual void initialize(valuet &value);

  row_valuet between(const row_valuet &lower, const row_valuet &upper);
  bool less_than(const row_valuet &v1, const row_valuet &v2);

  exprt get_row_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_post_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_pre_constraint(const rowt &row, const templ_valuet &value);
  exprt get_row_post_constraint(const rowt &row, const templ_valuet &value);

  exprt to_pre_constraints(const templ_valuet &value);
  void make_not_post_constraints(const templ_valuet &value,
			   exprt::operandst &cond_exprs, 
			   exprt::operandst &value_exprs);

  row_valuet get_row_value(const rowt &row, const templ_valuet &value);
  void set_row_value(const rowt &row, const row_valuet &row_value, templ_valuet &value);

  row_valuet get_max_row_value(const rowt &row);
  row_valuet get_min_row_value(const rowt &row);

  virtual void output_value(std::ostream &out, const valuet &value, const namespacet &ns) const;
  virtual void output_domain(std::ostream &out, const namespacet &ns) const;

  unsigned template_size();
  bool is_row_value_inf(const row_valuet & row_value) const;
  bool is_row_value_neginf(const row_valuet & row_value) const;

  virtual void project_on_loops(const valuet &value, exprt &result);
  virtual void project_on_inout(const valuet &value, exprt &result);

protected:
  templatet &templ;
  
};

void make_interval_template(template_domaint::templatet &templ,
			   const template_domaint::var_listt &vars,
			   const template_domaint::var_guardst &pre_guards,
			   const template_domaint::var_guardst &post_guards,
			   const template_domaint::kindst &kinds,
                           const namespacet &ns);
void make_zone_template(template_domaint::templatet &templ,
			   const template_domaint::var_listt &vars,
			   const template_domaint::var_guardst &pre_guards,
			   const template_domaint::var_guardst &post_guards,
			   const template_domaint::kindst &kinds,
                           const namespacet &ns);
void make_octagon_template(template_domaint::templatet &templ,
			   const template_domaint::var_listt &vars,
			   const template_domaint::var_guardst &pre_guards,
			   const template_domaint::var_guardst &post_guards,
			   const template_domaint::kindst &kinds,
                           const namespacet &ns);

constant_exprt simplify_const(const exprt &expr);

#endif
