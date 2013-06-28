/*******************************************************************\

Module: Definition Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
    out << d_it->first << ": " << d_it->second->location_number;
    out << std::endl;
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
    def_map[id]=from;
    assigned.insert(id);
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

bool ssa_domaint::merge(const ssa_domaint &b, locationt l)
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
      def_map[id]=d_it_b->second;
      result=true;
      #ifdef DEBUG
      std::cout << "SETTING " << id << ": " << d_it_b->second->location_number << std::endl;
      #endif
    }
    else
    {
      if(d_it_a->second!=d_it_b->second)
      {
        // aarg! data coming from two different places!
        d_it_a->second=l; // new phi node
        result=true;
        phi_nodes.insert(id);
        #ifdef DEBUG
        std::cout << "MERGING " << id << ": " << l->location_number << std::endl;
        #endif
     }
      else
      {
        #ifdef DEBUG
        std::cout << "AGREE " << id << ": " << d_it_b->second->location_number << std::endl;
        #endif
      }
      
    }
  }
  
  return result;
}
