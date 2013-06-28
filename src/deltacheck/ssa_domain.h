/*******************************************************************\

Module: Definition Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SOURCE_DOMAIN_H
#define CPROVER_SOURCE_DOMAIN_H

#include <analyses/static_analysis.h>
#include <analyses/interval_analysis.h>

class ssa_domaint:public domain_baset
{
public:
  // identifier to its definition (source) location
  typedef std::map<irep_idt, locationt> def_mapt;
  def_mapt def_map;
  
  typedef std::map<irep_idt, std::set<locationt> > phi_nodest;
  phi_nodest phi_nodes;
  
  virtual void transform(
    const namespacet &ns,
    locationt from,
    locationt to);
              
  virtual void output(
    const namespacet &ns,
    std::ostream &out) const;

  bool merge(
    const ssa_domaint &b,
    locationt l);
    
protected:
  void assign(const exprt &lhs, locationt from);
};

#endif
