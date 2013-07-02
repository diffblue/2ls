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
  struct def_entryt
  {
    locationt def;
    locationt source;
  };

  friend inline std::ostream & operator << (
    std::ostream &out, const def_entryt &d)
  {
    return out << d.def->location_number << " from "
               << d.source->location_number;
  }
  
  friend inline bool operator < (
    const def_entryt &a, const def_entryt &b)
  {
    if(a.def==b.def)
      return a.source < b.source;
    else
      return a.def < b.def;
  }
  
  typedef std::map<irep_idt, def_entryt> def_mapt;
  def_mapt def_map;

  // the phi nodes map identifiers to the definitions
  // of the incoming branches
  typedef std::map<irep_idt, std::set<def_entryt> > phi_nodest;
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
    locationt to);
    
protected:
  void assign(const exprt &lhs, locationt from);
};

#endif
