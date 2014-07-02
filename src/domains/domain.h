#ifndef CPROVER_DOMAIN_H
#define CPROVER_DOMAIN_H

#include <iostream>
#include <util/std_expr.h>
#include <langapi/language_util.h>

class domaint
{
public:

  virtual ~domaint() {}

  typedef symbol_exprt vart;
  typedef std::vector<vart> var_listt;

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

  static kindt merge_kinds(kindt k1, kindt k2)
  {
    return (k1==OUT || 
            k2==OUT ?  (k1==LOOP || 
                        k2==LOOP ?  OUTL : OUT) :
                       (k1==LOOP || k2==LOOP ? LOOP :  IN));
  }


};

#endif
