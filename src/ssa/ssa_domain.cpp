/*******************************************************************\

Module: Definition Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>

#include "object_id.h"
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
  if(from->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(from->code);
    assign(code_assign.lhs(), from, ai, ns);
  }
  else if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    assign(code_decl.symbol(), from, ai, ns);
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

Function: ssa_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_domaint::assign(
  const exprt &lhs, locationt from,
  ai_baset &ai,
  const namespacet &ns)
{
  if(lhs.id()==ID_typecast)
  {
    assign(to_typecast_expr(lhs).op(), from, ai, ns);
    return;
  }
  else if(lhs.id()==ID_if)
  {
    assign(to_if_expr(lhs).true_case(), from, ai, ns);
    assign(to_if_expr(lhs).false_case(), from, ai, ns);
    return;
  }

  const typet &lhs_type=ns.follow(lhs.type());
  
  if(lhs_type.id()==ID_struct)
  {
    // Are we assigning an entire struct?
    // If so, need to split into pieces, recursively.
  
    const struct_typet &struct_type=to_struct_type(lhs_type);
    const struct_typet::componentst &components=struct_type.components();
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      member_exprt new_lhs(lhs, it->get_name(), it->type());
      assign(new_lhs, from, ai, ns); // recursive call
    }
    
    return; // done
  }
  else if(lhs_type.id()==ID_union)
  {
    // todo
  }
  
  const ssa_objectt ssa_object(lhs);
  
  if(ssa_object)
  {
    assign(ssa_object, from, ai, ns);

    if(lhs.id()==ID_dereference)
    {
      // this might alias other stuff
      const std::set<ssa_objectt> &objects=
        static_cast<const ssa_ait &>(ai).objects;
        
      for(std::set<ssa_objectt>::const_iterator
          o_it=objects.begin();
          o_it!=objects.end();
          o_it++)
      {
        if(may_alias(*o_it, ssa_object))
          assign(*o_it, from, ai, ns);
      }
    }    
  }
}

/*******************************************************************\

Function: ssa_domaint::may_alias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ssa_domaint::may_alias(
  const ssa_objectt &o1, const ssa_objectt &o2)
{
  return false;
}

/*******************************************************************\

Function: ssa_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_domaint::assign(
  const ssa_objectt &lhs,
  locationt from,
  ai_baset &,
  const namespacet &)
{
  def_entryt &def_entry=def_map[lhs.get_identifier()];
  def_entry.def.loc=from;
  def_entry.def.kind=deft::ASSIGNMENT;
  def_entry.source=from;
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
