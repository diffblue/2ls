/*******************************************************************\

Module: Discover the Guards of Basic Blocks

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GUARD_DOMAIN_H
#define CPROVER_GUARD_DOMAIN_H

#include <analyses/static_analysis.h>
#include <analyses/interval_analysis.h>

class guard_domaint:public domain_baset
{
public:
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

  // We may be under some set of guards.
  typedef std::vector<guardt> guardst;
  guardst guards;
  
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
