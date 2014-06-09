#include "template_domain.h"

#include <util/arith_tools.h>
#include <util/ieee_float.h>

template_domaint::row_valuet template_domaint::between(
  const row_valuet &lower, const row_valuet &upper)
{
  if(lower.type()==upper.type() && 
     (lower.type().id()==ID_signedbv || lower.type().id()==ID_unsignedbv))
  {
    mp_integer vlower, vupper;
    to_integer(lower, vlower);
    to_integer(upper, vupper);
    return from_integer((vupper-vlower)/2,lower.type());
  }
  if(lower.type().id()==ID_floatbv && upper.type().id()==ID_floatbv)
  {
    ieee_floatt vlower(to_constant_expr(lower));
    ieee_floatt vupper(to_constant_expr(upper));
    vupper -= vlower;
    ieee_floatt two;
    two.from_float(2.0);
    vupper /= two;
    return vupper.to_expr();
  }
  assert(false); //types do not match
}

exprt template_domaint::make_row_constraint(const rowt &row, const row_valuet &value)
{
  assert(row<templ.size());
  return binary_relation_exprt(templ[row],ID_le,value);
}

exprt template_domaint::make_constraints(const valuet &inv)
{
  assert(inv.size()==templ.size());
  exprt::operandst c; 
  for(unsigned row = 0; row<templ.size(); row++)
  {
    c.push_back(binary_relation_exprt(templ[row],ID_le,inv[row]));
  }
  return conjunction(c); 
}

inline template_domaint::row_valuet template_domaint::get_value(
  const rowt &row, const valuet &inv)
{
  assert(row<inv.size());
  assert(inv.size()==templ.size());
  return inv[row];
}

void make_interval_template(template_domaint::templatet &templ, 
  const predicatet::state_var_listt &vars)
{
  templ.clear();
  templ.reserve(2*vars.size());
  for(predicatet::state_var_listt::const_iterator v = vars.begin(); 
      v!=vars.end(); v++)
  {
    templ.push_back(*v);
    templ.push_back(unary_minus_exprt(*v,v->type()));
  }
}

void make_zone_template(template_domaint::templatet &templ, 
  const predicatet::state_var_listt &vars)
{ 
  templ.clear();
  templ.reserve(2*vars.size()+vars.size()*(vars.size()-1));
  for(predicatet::state_var_listt::const_iterator v1 = vars.begin(); 
      v1!=vars.end(); v1++)
  {
    templ.push_back(*v1);
    templ.push_back(unary_minus_exprt(*v1,v1->type()));
    for(predicatet::state_var_listt::const_iterator v2 = v1; 
        v2!=vars.end(); v2++)
    {
      templ.push_back(minus_exprt(*v1,*v2));
      templ.push_back(minus_exprt(*v2,*v1));
    }
  }
}

void make_octagon_template(template_domaint::templatet &templ,
  const predicatet::state_var_listt &vars)
{
  templ.clear();
  templ.reserve(2*vars.size()+2*vars.size()*(vars.size()-1));
  for(predicatet::state_var_listt::const_iterator v1 = vars.begin(); 
      v1!=vars.end(); v1++)
  {
    templ.push_back(*v1);
    templ.push_back(unary_minus_exprt(*v1,v1->type()));
    for(predicatet::state_var_listt::const_iterator v2 = v1; 
        v2!=vars.end(); v2++)
    {
      templ.push_back(minus_exprt(*v1,*v2));
      templ.push_back(minus_exprt(*v2,*v1));
      templ.push_back(plus_exprt(*v1,*v2));
      templ.push_back(plus_exprt(*v2,*v1));
    }
  }
}
