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
  // definition and source location for an identifier
  struct def_entryt
  {
    locationt source, def;
  };

  friend inline std::ostream & operator << (
    std::ostream &out, const def_entryt &d)
  {
    return out << d.def->location_number << " from "
               << d.source->location_number;
  }
  
  typedef std::map<irep_idt, def_entryt> def_mapt;
  def_mapt def_map;

  // the phi nodes map identifiers to incoming branches:
  // map from source to definition
  typedef std::map<irep_idt, std::map<locationt, locationt> > phi_nodest;
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
