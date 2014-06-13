#ifndef CPROVER_TEMPLATE_DOMAIN_H
#define CPROVER_TEMPLATE_DOMAIN_H
#include "predicate.h"

#include <util/std_expr.h>

class template_domaint
{
public:
  typedef unsigned rowt;
  typedef exprt row_exprt; 
  typedef std::vector<exprt> guardst; 
  typedef std::vector<row_exprt> row_exprst; 
  typedef constant_exprt row_valuet; // "bound"
  typedef std::vector<row_valuet> valuet;
  typedef std::vector<symbol_exprt> var_listt;
  typedef std::vector<std::pair<symbol_exprt,exprt> > var_guardst; 

  typedef struct 
  {
    guardst guards;
    row_exprst rows;

    unsigned size() { return rows.size(); 
} 
  } templatet;

 template_domaint(templatet &_template) :
  templ(_template) 
 {}

  void bottom(valuet &value);
  void set_to_top(const var_listt &top_vars, valuet &value);

  row_valuet between(const row_valuet &lower, const row_valuet &upper);
  bool leq(const row_valuet &v1, const row_valuet &v2);

  exprt get_row_constraint(const rowt &row, const row_valuet &row_value);
  exprt get_row_constraint(const rowt &row, const valuet &value);

  exprt to_constraints(const valuet &value);
  void make_not_constraints(const valuet &value,
			   exprt::operandst &cond_exprs, 
			   exprt::operandst &value_exprs);

  row_valuet get_row_value(const rowt &row, const valuet &inv);
  void set_row_value(const rowt &row, const row_valuet &row_value, valuet &value);

  row_valuet get_max_row_value(const rowt &row);

  void output_value(std::ostream &out, const valuet &value, const namespacet &ns) const;
  void output_template(std::ostream &out, const namespacet &ns) const;

  unsigned template_size();
  bool is_row_value_inf(const row_valuet & row_value) const;
  bool is_row_value_neginf(const row_valuet & row_value) const;

protected:
  templatet &templ;
  
};

void make_interval_template(template_domaint::templatet &templ,
			   const template_domaint::var_guardst &var_guards);
void make_zone_template(template_domaint::templatet &templ,
			   const template_domaint::var_guardst &var_guards);
void make_octagon_template(template_domaint::templatet &templ,
			   const template_domaint::var_guardst &var_guards);

#endif
