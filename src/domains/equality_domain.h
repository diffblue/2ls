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
  typedef std::set<var_pairt> var_pairst;
  typedef std::set<unsigned> index_sett;

  equality_domaint(
    const var_listt &vars, 
    const guardst &pre_guards,
    const guardst &post_guards,
    const kindst &kinds,
    const namespacet &ns) 
  {
    make_template(vars,pre_guards,post_guards,kinds,ns);
  }

  class equ_valuet : public valuet 
  {
   public:

    union_find<vart> equs;
    index_sett disequs;
  };

  typedef struct 
  {
    guardst pre_guards;
    guardst post_guards;
    std::vector<equality_domaint::var_pairt> var_pairs;
    kindst kinds;

    unsigned size() const { return var_pairs.size(); } 
  } templatet;

  virtual void initialize(valuet &value);

  exprt get_pre_equ_constraint(unsigned index);
  exprt get_post_not_equ_constraint(unsigned index);
  exprt get_pre_disequ_constraint(unsigned index);
  exprt get_post_not_disequ_constraint(unsigned index);

  void set_equal(unsigned index, equ_valuet &value);
  void set_disequal(unsigned index, equ_valuet &value);

  virtual void output_value(std::ostream &out, const valuet &value, 
    const namespacet &ns) const;
  virtual void output_domain(std::ostream &out, const namespacet &ns) const;

  virtual void project_on_loops(const valuet &value, exprt &result);
  virtual void project_on_inout(const valuet &value, exprt &result);

  void get_index_set(index_sett &indices); 
  const var_pairt &get_var_pair(unsigned index);

 protected:
  templatet templ;

  void make_template(
    const var_listt &vars,
    const guardst &pre_guards,
    const guardst &post_guards,
    const kindst &kind,
    const namespacet &ns);
};

#endif
