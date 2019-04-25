/*******************************************************************\

Module: Definition Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Definition Domain

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>

#include "ssa_domain.h"

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
    for(loc_def_mapt::const_iterator
        n_it=p_it->second.begin();
        n_it!=p_it->second.end();
        n_it++)
    {
      // this maps source -> def
      out << "PHI " << p_it->first << ": "
          << (*n_it).second
          << " from "
          << (*n_it).first << "\n";
    }
  }
}

void ssa_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  if(from->is_assign() || from->is_decl() || from->is_function_call())
  {
    const auto &assignments=static_cast<ssa_ait &>(ai).assignments;
    const std::set<ssa_objectt> &assigns=assignments.get(from);

    for(std::set<ssa_objectt>::const_iterator
        o_it=assigns.begin();
        o_it!=assigns.end();
        o_it++)
    {
      if(o_it->get_expr().get_bool("#is_rhs_assign") &&
         is_pointed(o_it->get_root_object()))
      {
        // the second part excluded cases
        // when a result of malloc is at the right-handed side
        const auto object_ai_it=
          static_cast<ssa_ait &>(ai)[from].def_map.find(o_it->get_identifier());
        if(object_ai_it!=static_cast<ssa_ait &>(ai)[from].def_map.end() &&
           object_ai_it->second.def.is_assignment())
        {
          const exprt pointer=
            get_pointer(
              o_it->get_root_object(),
              pointed_level(o_it->get_root_object())-1);
          const auto def_pointer=
            static_cast<ssa_ait &>(ai)[from]
              .def_map.find(
                ssa_objectt(pointer, ns).get_identifier())->second.def;
          if(!def_pointer.is_assignment() ||
             def_pointer.loc->location_number<
               object_ai_it->second.def.loc->location_number)
          {
            continue;
          }
        }
      }
      irep_idt identifier=o_it->get_identifier();

      def_entryt &def_entry=def_map[identifier];
      def_entry.def.loc=from;
      def_entry.source=from;
      auto guard_it=assignments.alloc_guards_map.find({from, *o_it});
      if(guard_it!=assignments.alloc_guards_map.end())
      {
        def_entry.def.kind=deft::ALLOCATION;
        def_entry.def.guard=guard_it->second;
      }
      else
        def_entry.def.kind=deft::ASSIGNMENT;
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
      loc_def_mapt &phi_node=p_it->second;
      phi_node[d_it_b->second.source->location_number]=d_it_b->second.def;
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
      loc_def_mapt &phi_node=phi_nodes[id];

      phi_node[d_it_a->second.source->location_number]=d_it_a->second.def;
      phi_node[d_it_b->second.source->location_number]=d_it_b->second.def;

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

ssa_domaint::def_mapt::const_iterator ssa_domaint::get_object_allocation_def(
  const irep_idt &id,
  const ssa_domaint::def_mapt &def_map)
{
  auto def=def_map.find(id);
  std::string id_str=id2string(id);
  if(def!=def_map.end() &&
     def->second.def.kind==deft::ASSIGNMENT &&
     id_str.find("ssa::dynamic_object$")!=std::string::npos)
  {
    // Check if corresponding dynamic object has been allocated in that branch
    std::string dyn_obj_id=id_str.substr(0, id_str.find_first_of("."));
    auto dyn_obj_def=def_map.find(dyn_obj_id);
    if(dyn_obj_def!=def_map.end() &&
       dyn_obj_def->second.def.kind==deft::ALLOCATION)
      return dyn_obj_def;
  }
  return def_map.end();
}

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
