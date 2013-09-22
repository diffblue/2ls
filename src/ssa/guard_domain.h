/*******************************************************************\

Module: Discover the Guards of Basic Blocks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GUARD_DOMAIN_H
#define CPROVER_GUARD_DOMAIN_H

#include <analyses/ai.h>

class guard_domaint:public ai_domain_baset
{
public:
  // the constructor builds 'bottom'
  inline guard_domaint():unreachable(true)
  {
  }

  // A guard is defined by the locatio of the branch;
  // It may be negated, for the else-branch.
  struct guardt
  {
  public:
    locationt branch;
    bool truth;
    
    explicit guardt(locationt _branch):branch(_branch), truth(true)
    {
    }

    guardt(locationt _branch, bool _truth):branch(_branch), truth(_truth)
    {
    }
  };
  
  inline friend bool operator==(const guardt &a, const guardt &b)
  {
    return a.truth==b.truth &&
           a.branch->location_number==b.branch->location_number;
  }
  
  virtual void make_entry_state()
  {
    // this is 'top'
    unreachable=false;
    guards.clear();
  }

  // We may be under some set of guards.
  typedef std::vector<guardt> guardst;
  guardst guards;
  
  bool unreachable;
  
  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to);
              
  virtual void output(
    const namespacet &ns,
    std::ostream &out) const;

  bool merge(
    const guard_domaint &b,
    locationt to);
};

#endif
