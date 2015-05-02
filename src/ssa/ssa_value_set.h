/*******************************************************************\

Module: A flow-insensitive value set analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_VALUE_SET_H
#define CPROVER_SSA_VALUE_SET_H

#include <analyses/ai.h>

#include "ssa_object.h"

class ssa_value_domaint:public ai_domain_baset
{
public:
  virtual void transform(locationt, locationt, ai_baset &, const namespacet &);
  virtual void output(std::ostream &, const ai_baset &, const namespacet &) const;
  bool merge(const ssa_value_domaint &, locationt, locationt);

  struct valuest
  {
  public:
    typedef std::set<ssa_objectt> value_sett;
    value_sett value_set;
    bool offset, null, unknown, integer_address;
    unsigned alignment;
    
    inline valuest():
      offset(false), null(false), unknown(false), integer_address(false),
      alignment(0)
    {
    }
    
    void output(std::ostream &, const namespacet &) const;
    
    bool merge(const valuest &src);
    
    inline void clear()
    {
      *this=valuest();
    }
    
    bool empty() const
    {
      return value_set.empty() && !null && !unknown && !integer_address;
    }
  };
  
  // maps objects to values
  typedef std::map<ssa_objectt, valuest> value_mapt;
  value_mapt value_map;
  
  const valuest operator()(const exprt &src, const namespacet &ns) const
  {
    valuest tmp;
    assign_rhs_rec(tmp, src, ns, false, 0);
    return tmp;
  }
  
protected:
  void assign_lhs_rec(
    const exprt &lhs, const exprt &rhs,
    const namespacet &,
    bool add=false);

  void assign_rhs_rec(
    valuest &lhs, const exprt &rhs,
    const namespacet &,
    bool offset,
    unsigned alignment) const;

  void assign_rhs_rec_address_of(
    valuest &lhs, const exprt &rhs,
    const namespacet &,
    bool offset,
    unsigned alignment) const;

  static unsigned merge_alignment(unsigned a, unsigned b)
  {
    // could use lcm here
    if(a==b) return a;
    if(a==0) return b;
    if(b==0) return a;
    return 1;
  }
};

class ssa_value_ait:public ait<ssa_value_domaint>
{
public:
  ssa_value_ait(
    const goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(goto_function, ns);
  }

protected:
  friend class ssa_value_domaint;
};

#endif
