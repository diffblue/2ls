/*******************************************************************\

Module: Definition Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/std_expr.h>

#include "def_domain.h"

/*******************************************************************\

Function: def_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void def_domaint::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(def_mapt::const_iterator
      d_it=def_map.begin();
      d_it!=def_map.end();
      d_it++)
  {
    out << d_it->first << ":";
    for(std::set<locationt>::const_iterator
        s_it=d_it->second.begin(); s_it!=d_it->second.end(); s_it++)
    {
      if(s_it!=d_it->second.begin()) out << ",";
      out << " " << (*s_it)->location_number;
    }
    
    out << std::endl;
  }
}

/*******************************************************************\

Function: def_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void def_domaint::transform(
  const namespacet &ns,
  locationt from,
  locationt to)
{
  if(from->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(from->code);
    assign(code_assign.lhs(), from);
  }
}

/*******************************************************************\

Function: def_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void def_domaint::assign(const exprt &lhs, locationt from)
{
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(lhs).get_identifier();
    std::set<locationt> &def_set=def_map[id];
    def_set.clear();
    def_set.insert(from);
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

Function: def_domaint::merge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool def_domaint::merge(const def_domaint &b)
{
  bool result=false;

  // should traverse both maps simultaneously
  for(def_mapt::const_iterator
      d_it=b.def_map.begin();
      d_it!=b.def_map.end();
      d_it++)
  {
    const std::set<locationt> &src=d_it->second;
    std::set<locationt> &dest=def_map[d_it->first];
    unsigned dest_size_before=dest.size();

    // we hope the STL optimizes the below to be linear in src.size()
    dest.insert(src.begin(), src.end());
    
    if(dest.size()!=dest_size_before) result=true;
  }
  
  return result;
}
