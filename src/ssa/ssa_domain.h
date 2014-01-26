/*******************************************************************\

Module: Definition Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SSA_DOMAIN_H
#define CPROVER_SSA_DOMAIN_H

#include <analyses/ai.h>

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
    
protected:
  void assign(
    const exprt &lhs, locationt from,
    const namespacet &ns);
};

class ssa_ait:public ait<ssa_domaint>
{
protected:
  // The below is needed to make the entry point get a source
  // for the function parameters.
  
  virtual void initialize(const goto_functionst::goto_functiont &goto_function)
  {
    ait<ssa_domaint>::initialize(goto_function);

    // make entry instruction have a source for the parameters
    if(!goto_function.body.instructions.empty())
    {
      locationt e=goto_function.body.instructions.begin();
      ssa_domaint &entry=operator[](e);
      const code_typet::parameterst &parameters=goto_function.type.parameters();
      for(code_typet::parameterst::const_iterator p_it=parameters.begin();
          p_it!=parameters.end();
          p_it++)
      {
        irep_idt id=p_it->get_identifier();
        entry.def_map[id].source=e;
        entry.def_map[id].def.loc=e;
        entry.def_map[id].def.kind=ssa_domaint::deft::INPUT;
      }
    }
  }
};

#endif
