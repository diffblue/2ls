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
  const namespacet &ns,
  std::ostream &out) const
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
    for(std::set<def_entryt>::const_iterator
        n_it=p_it->second.begin();
        n_it!=p_it->second.end();
        n_it++)
    {
      out << "PHI " << p_it->first << ": "
          << (*n_it) << "\n";
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
  const namespacet &ns,
  locationt from,
  locationt to)
{
  if(from->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(from->code);
    assign(code_assign.lhs(), from);
  }
  else if(from->is_decl())
  {
    const code_declt &code_decl=to_code_decl(from->code);
    assign(code_decl.symbol(), from);
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

void ssa_domaint::assign(const exprt &lhs, locationt from)
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(lhs).get_identifier();
    def_entryt &def_entry=def_map[id];
    def_entry.def=from;
    def_entry.source=from;
  }
  else if(lhs.id()==ID_member || lhs.id()==ID_index || lhs.id()==ID_typecast)
  {
    assign(lhs.op0(), from);
  }
  else if(lhs.id()==ID_dereference)
  {
  }
}

/*******************************************************************\

Function: ssa_domaint::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ssa_domaint::merge(
  const ssa_domaint &b,
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
  
    def_mapt::iterator d_it_a=def_map.find(id);
    if(d_it_a==def_map.end())
    {
      // no entry in 'this' yet, create entry
      def_map[id]=d_it_b->second;
      result=true;

      #ifdef DEBUG
      std::cout << "SETTING " << id << ": " << def_map[id] << "\n";
      #endif
    }
    else
    {
      // we have two entries, compare
      
      if(d_it_a->second.def!=d_it_b->second.def)
      {
        // same source?
        if(d_it_a->second.source==d_it_b->second.source)
        {
          d_it_a->second.def=d_it_b->second.def;
          result=true;

          #ifdef DEBUG
          std::cout << "OVERWRITING " << id << ": " << def_map[id] << "\n";
          #endif
        }
        else
        {
          // Arg! Data coming from two different places!
          // Produce new phi node.
          std::set<def_entryt> &phi_node=phi_nodes[id];
          
          phi_node.insert(d_it_a->second);
          phi_node.insert(d_it_b->second);
          
          // this node is now the new source        
          d_it_a->second.def=to;
          d_it_a->second.source=to;

          result=true;

          #ifdef DEBUG
          std::cout << "MERGING " << id << ": " << d_it_b->second << "\n";
          #endif
        }
     }
      else
      {
        #ifdef DEBUG
        std::cout << "AGREE " << id << ": " << d_it_b->second << "\n";
        #endif
      }
      
    }
  }
  
  return result;
}
