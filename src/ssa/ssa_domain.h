/*******************************************************************\

Module: Definition Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_DOMAIN_H
#define CPROVER_SSA_DOMAIN_H

#include <analyses/ai.h>

#include "ssa_object.h"

class ssa_domaint:public ai_domain_baset
{
public:
  // sources for identifiers
  struct deft
  {
    deft():kind(ASSIGNMENT) { }
    typedef enum { INPUT, ASSIGNMENT, PHI } kindt;
    kindt kind;
    locationt loc;
    
    inline bool is_input() const { return kind==INPUT; }
    inline bool is_assignment() const { return kind==ASSIGNMENT; }
    inline bool is_phi() const { return kind==PHI; }
  };

  friend inline bool operator == (const deft &a, const deft &b)
  {
    return a.kind==b.kind && a.loc==b.loc;
  }

  friend inline std::ostream & operator << (
    std::ostream &out, const deft &d)
  {
    switch(d.kind)
    {
    case deft::INPUT: out << "INPUT"; break;
    case deft::ASSIGNMENT: out << d.loc->location_number; break;
    case deft::PHI: out << "PHI" << d.loc->location_number; break;
    }
    return out;
  }

  // definition and source for an identifier
  struct def_entryt
  {
    def_entryt() { }
    deft def;
    locationt source; // information from?
  };

  friend inline std::ostream & operator << (
    std::ostream &out, const def_entryt &d)
  {
    return out << d.def << " from " << d.source->location_number;
  }
  
  typedef std::map<irep_idt, def_entryt> def_mapt;
  def_mapt def_map;
  
  // the phi nodes map identifiers to incoming branches:
  // map from source to definition
  typedef std::map<irep_idt, std::map<locationt, deft> > phi_nodest;
  phi_nodest phi_nodes;
  
  // stuff assigned at this location
  std::set<irep_idt> assigned_objects;
  
  inline bool is_assigned(const ssa_objectt &object) const
  {
    return assigned_objects.find(object.get_identifier())!=
           assigned_objects.end();
  }
  
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai,
    const namespacet &ns);
              
  virtual void output(
    std::ostream &out,
    const ai_baset &ai,
    const namespacet &ns) const;

  bool merge(
    const ssa_domaint &b,
    locationt from,
    locationt to);
    
  static bool may_alias(
    const ssa_objectt &o1,
    const ssa_objectt &o2);

protected:
  void assign(
    const exprt &lhs, locationt from,
    ai_baset &ai,
    const namespacet &ns);
    
  void assign(
    const ssa_objectt &lhs, locationt from,
    ai_baset &ai,
    const namespacet &ns);    
};

class ssa_ait:public ait<ssa_domaint>
{
public:
  typedef std::set<ssa_objectt> objectst;

  explicit ssa_ait(const objectst &_objects):
    objects(_objects)
  {
  }

protected:
  const objectst &objects;
  
  friend class ssa_domaint;

  // The overload below is needed to make the entry point get a source
  // for the function parameters.
  virtual void initialize(const goto_functionst::goto_functiont &goto_function);
};

#endif
