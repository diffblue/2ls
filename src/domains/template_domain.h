#ifndef CPROVER_TEMPLATE_DOMAIN_H
#define CPROVER_TEMPLATE_DOMAIN_H

#include <util/std_expr.h>

class template_domaint
{
public:
  typedef exprt rowt; 
  typedef std::vector<rowt> templatet; 
  typedef constant_exprt valuet; // "bound"
  typedef std::vector<valuet> invariantt;

  template_domaint() {}

  valuet between(const valuet &lower, const valuet &upper);

  exprt make_row_constraint(const rowt &row, const valuet &value);
  valuet make_row_constraint(const rowt &row, const valuet &value);

protected:
  templatet template;
  

};

#endif
