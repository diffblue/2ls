#ifndef CPROVER_TEMPLATE_DOMAIN_H
#define CPROVER_TEMPLATE_DOMAIN_H

#include <util/std_expr.h>

class template_domaint
{
public:
  typedef unsigned rowt;
  typedef exprt row_exprt; 
  typedef std::vector<row_exprt> templatet; 
  typedef constant_exprt row_valuet; // "bound"
  typedef std::vector<row_valuet> valuet;

 template_domaint(templatet &_template) :
   templ(_template) 
 {}

  row_valuet between(const row_valuet &lower, const row_valuet &upper);

  exprt make_row_constraint(const rowt &row, const row_valuet &value);
  exprt make_constraints(const valuet &inv);
  inline row_valuet get_value(const rowt &row, const valuet &inv);

  void output_invariant(std::ostream &out, const valuet &inv, const namespacet &ns) const;
  void output_template(std::ostream &out, const namespacet &ns) const;

protected:
  templatet templ;
  
};

void make_interval_template(template_domaint::templatet &templ,
			   const predicatet::state_var_listt &vars);
void make_zone_template(template_domaint::templatet &templ,
			   const predicatet::state_var_listt &vars);
void make_octagon_template(template_domaint::templatet &templ,
			   const predicatet::state_var_listt &vars);

#endif
