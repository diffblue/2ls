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
  const irep_idt &from_function,
  trace_ptrt trace_from,
  const irep_idt &to_function,
  trace_ptrt trace_to,
  ai_baset &ai,
  const namespacet &ns)
{
  locationt from{trace_from->current_location()};

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
    const irep_idt &id=from->dead_symbol().get_identifier();
    def_map.erase(id);
  }

  // update source in all defs
  for(def_mapt::iterator
      d_it=def_map.begin(); d_it!=def_map.end(); d_it++)
    d_it->second.source=from;
}

bool ssa_domaint::merge(
  const ssa_domaint &b,
  trace_ptrt trace_from,
  trace_ptrt trace_to)
{
  locationt to{trace_to->current_location()};

  bool result=has_values.is_false() && !b.has_values.is_false();

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


void ssa_ait::initialize(
  const irep_idt &function_id,
  const goto_functionst::goto_functiont &goto_function)
{
  ait<ssa_domaint>::initialize(function_id, goto_function);
  forall_goto_program_instructions(i_it, goto_function.body)
    get_state(i_it).make_bottom();

  // Make entry instruction have a source for the all objects.

  if(!goto_function.body.instructions.empty())
  {
    locationt e=goto_function.body.instructions.begin();
    auto entry_s=entry_state(goto_function.body);
    ssa_domaint &entry=dynamic_cast<ssa_domaint &>(get_state(entry_s));

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
