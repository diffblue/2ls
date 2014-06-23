#ifndef CPROVER_EQUALITY_DOMAIN_H
#define CPROVER_EQUALITY_DOMAIN_H

#include <util/std_expr.h>
#include <util/union_find.h>

#include <set>
 
#include "domain.h"

class equality_domaint : public domaint
{
public:
 typedef std::pair<vart,vart> var_pairt;

 equality_domaint(const var_listt &_vars, const kindst &_kinds) :
  vars(_vars), kinds(_kinds) 
 {}

  class equ_valuet : public valuet 
  {
   public:

    union_find<vart> equs;
    std::set<var_pairt> disequs;
  };

  virtual void initialize(valuet &value);

  exprt get_pre_equ_constraint(const var_pairt &vv);
  exprt get_post_not_equ_constraint(const var_pairt &vv);
  exprt get_pre_disequ_constraint(const var_pairt &vv);
  exprt get_post_not_disequ_constraint(const var_pairt &vv);

  void set_equal(const var_pairt &vv, equ_valuet &value);
  void set_disequal(const var_pairt &vv, equ_valuet &value);

  virtual void output_value(std::ostream &out, const valuet &value, 
    const namespacet &ns) const;
  virtual void output_domain(std::ostream &out, const namespacet &ns) const;

  virtual void project_on_loops(const valuet &value, exprt &result);
  virtual void project_on_inout(const valuet &value, exprt &result);

  const var_listt &get_vars() const { return vars; }
  

 protected:
  var_listt vars;
  kindst kinds;
};

#endif
