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
    
    inline valuest():
      offset(false), null(false), unknown(false), integer_address(false)
    {
    }
    
    void output(std::ostream &, const namespacet &) const;
  };
  
  // maps objects to values
  typedef std::map<ssa_objectt, valuest> value_mapt;
  value_mapt value_map;
  
protected:
  void assign(
    const exprt &lhs, const exprt &rhs,
    const ssa_objectst &,
    const namespacet &);
};

class ssa_value_ait:public ait<ssa_value_domaint>
{
public:
  ssa_value_ait(const ssa_objectst &_ssa_objects):ssa_objects(_ssa_objects)
  {
  }

protected:
  const ssa_objectst &ssa_objects;
  
  friend class ssa_value_domaint;
};

#endif
