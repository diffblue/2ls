#ifndef CPROVER_DOMAIN_H
#define CPROVER_DOMAIN_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <langapi/language_util.h>
#include <util/replace_expr.h>

class domaint
{
public:
  domaint(replace_mapt &_renaming_map) : renaming_map(_renaming_map) {}
  virtual ~domaint() {}

  typedef exprt vart;
  typedef std::vector<vart> var_listt;
  typedef std::set<vart> var_sett;

  typedef enum {LOOP, IN, OUT, OUTL} kindt;

  typedef exprt guardt; 

  typedef struct {
    guardt pre_guard;
    guardt post_guard;
    vart var;
    kindt kind;
  } var_spect;

  typedef std::vector<var_spect> var_specst; 

  class valuet {
   public:
    virtual ~valuet() {}
  };

  virtual void initialize(valuet &value) { assert(false); }

  // virtual exprt to_pre_constraints(const valuet &value) { assert(false); }
  // virtual void make_not_post_constraints(const valuet &value,
  //			   exprt::operandst &cond_exprs, 
  //			   exprt::operandst &value_exprs) { assert(false); }

  virtual void output_value(std::ostream &out, const valuet &value, 
    const namespacet &ns) const { assert(false); }
  virtual void output_domain(std::ostream &out, 
    const namespacet &ns) const { assert(false); }

  virtual void project_on_loops(const valuet &value, exprt &result) 
    { assert(false); }
  virtual void project_on_inout(const valuet &value, exprt &result) 
    { assert(false); }
  virtual void project_on_vars(const valuet &value, const var_sett &vars, exprt &result) 
    { assert(false); }

  static kindt merge_kinds(kindt k1, kindt k2);

  static void output_var_specs(std::ostream &out, const var_specst &var_specs,
			       const namespacet &ns);

 protected:
  replace_mapt &renaming_map;
  
  inline void rename(exprt &expr) { replace_expr(renaming_map, expr); }
  inline void rename(exprt::operandst &operands)
  {
    for(unsigned i=0; i<operands.size(); ++i)
      replace_expr(renaming_map, operands[i]);
  }

};

#endif
