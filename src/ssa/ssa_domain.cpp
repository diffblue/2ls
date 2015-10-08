/*******************************************************************\

Module: Definition Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>

#include "ssa_domain.h"

/*******************************************************************\

Function: ssa_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_domaint::output(
  std::ostream &out,
  const ai_baset &,
  const namespacet &ns) const
{
  for(def_mapt::const_iterator
      d_it=def_map.begin();
      d_it!=def_map.end();
      d_it++)
  {
    out << "DEF " << d_it->first << ": " << d_it->second << "\n";
  }

  for(phi_nodest::const_iterator
      p_it=phi_nodes.begin();
      p_it!=phi_nodes.end();
      p_it++)
  {
    for(std::map<locationt, deft>::const_iterator
        n_it=p_it->second.begin();
        n_it!=p_it->second.end();
        n_it++)
    {
      // this maps source -> def
      out << "PHI " << p_it->first << ": "
          << (*n_it).second
          << " from " 
          << (*n_it).first->location_number << "\n";
    }
  }
}

/*******************************************************************\

Function: ssa_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(from->is_assign() || from->is_decl() || from->is_function_call())
  {
    const std::set<ssa_objectt> &assigns=
      static_cast<ssa_ait &>(ai).assignments.get(from);

    for(std::set<ssa_objectt>::const_iterator
        o_it=assigns.begin();
        o_it!=assigns.end();
        o_it++)
    {
      irep_idt identifier=o_it->get_identifier();

      def_entryt &def_entry=def_map[identifier];
      def_entry.def.loc=from;
      def_entry.def.kind=deft::ASSIGNMENT;
      def_entry.source=from;
    }
  }
  else if(from->is_dead())
  {
    const code_deadt &code_dead=to_code_dead(from->code);
    const irep_idt &id=code_dead.get_identifier();
    def_map.erase(id);
  }
  
  // update source in all defs
  for(def_mapt::iterator
      d_it=def_map.begin(); d_it!=def_map.end(); d_it++)
    d_it->second.source=from;
}

/*******************************************************************\

Function: ssa_domaint::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ssa_domaint::merge(
  const ssa_domaint &b,
  locationt from,
  locationt to)
{
  bool result=false;
  
  // should traverse both maps simultaneously
  for(def_mapt::const_iterator
      d_it_b=b.def_map.begin();
      d_it_b!=b.def_map.end();
      d_it_b++)
  {
    const irep_idt &id=d_it_b->first;
 
    // check if we have a phi node for 'id'
  
    phi_nodest::iterator p_it=phi_nodes.find(id);
    if(p_it!=phi_nodes.end())
    {
      // yes, simply add to existing phi node
      std::map<locationt, deft> &phi_node=p_it->second;
      phi_node[d_it_b->second.source]=d_it_b->second.def;      
      // doesn't get propagated, don't set result to 'true'
      continue;
    }

    // have we seen this variable yet?
    def_mapt::iterator d_it_a=def_map.find(id);
    if(d_it_a==def_map.end())
    {
      // no entry in 'this' yet, simply create a new entry
      def_map[id]=d_it_b->second;
      result=true;

      #ifdef DEBUG
      std::cout << "SETTING " << id << ": " << def_map[id] << "\n";
      #endif
      continue;
    }

    // we have two entries, compare
    if(d_it_a->second.def==d_it_b->second.def)
    {
      #ifdef DEBUG
      std::cout << "AGREE " << id << ": " << d_it_b->second << "\n";
      #endif
      continue;
    }

    // Different definitions. Are they coming from the same source?
    if(d_it_a->second.source==d_it_b->second.source)
    {
      // Propagate the new definition for same source.
      d_it_a->second.def=d_it_b->second.def;
      result=true;

      #ifdef DEBUG
      std::cout << "OVERWRITING " << id << ": " << def_map[id] << "\n";
      #endif
    }
    else
    {
      // Arg! Data coming from two sources from two different definitions!
      // We produce a new phi node.
      std::map<locationt, deft> &phi_node=phi_nodes[id];

      phi_node[d_it_a->second.source]=d_it_a->second.def;
      phi_node[d_it_b->second.source]=d_it_b->second.def;
      
      // This phi node is now the new source.
      d_it_a->second.def.loc=to;
      d_it_a->second.def.kind=deft::PHI;
      d_it_a->second.source=to;

      result=true;

      #ifdef DEBUG
      std::cout << "MERGING " << id << ": " << d_it_b->second << "\n";
      #endif
    }
  }
  
  return result;
}

/*******************************************************************\

Function: ssa_ait::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_ait::initialize(const goto_functionst::goto_functiont &goto_function)
{
  ait<ssa_domaint>::initialize(goto_function);

  // Make entry instruction have a source for the all objects.

  if(!goto_function.body.instructions.empty())
  {
    locationt e=goto_function.body.instructions.begin();
    ssa_domaint &entry=operator[](e);
    
    #if 0
    // parameters
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
    #endif
    
    for(ssa_objectst::objectst::const_iterator
        o_it=assignments.ssa_objects.objects.begin();
        o_it!=assignments.ssa_objects.objects.end();
        o_it++)
    {
      irep_idt id=o_it->get_identifier();
      entry.def_map[id].source=e;
      entry.def_map[id].def.loc=e;
      entry.def_map[id].def.kind=ssa_domaint::deft::INPUT;
    }
  }
}
