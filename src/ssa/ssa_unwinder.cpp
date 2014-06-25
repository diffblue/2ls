/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel

\*******************************************************************/

#include <util/i2string.h>

#include "ssa_unwinder.h"

/*******************************************************************\

Function: ssa_unwindert::unwind

  Inputs:

 Outputs: 

 Purpose: unwinds all loops the given number of times

\*******************************************************************/

void ssa_unwindert::unwind(local_SSAt &SSA, unsigned unwind)
{
  // get all backwards edges
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
      local_SSAt::locationt loc = i_it->get_target(); 
    } 
  }
}

/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename(exprt &expr, unsigned index) 
{
  if(expr.id()==ID_symbol) 
  {
    symbol_exprt &sexpr = to_symbol_expr(expr);
    irep_idt id = id2string(sexpr.get_identifier())+"%"+i2string(index);
    sexpr.set_identifier(id);
  }
  for(exprt::operandst::iterator it = expr.operands().begin();
      it != expr.operands().end(); it++)
  {
    rename(*it);
  }
}

/*******************************************************************\

Function: ssa_inlinert::commit_nodes()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::commit_nodes(local_SSAt::nodest &nodes)
{
  //insert new nodes
  for(local_SSAt::nodest::const_iterator n_it = new_nodes.begin();
      n_it != new_nodes.end(); n_it++)
  {
    merge_into_nodes(nodes,n_it->first,n_it->second);
  }
  new_nodes.clear();
}

/*******************************************************************\

Function: ssa_inlinert::merge_node()

  Inputs:

 Outputs:

 Purpose: merges equalities and constraints of two nodes into the first one

\*******************************************************************/

void ssa_inlinert::merge_into_nodes(local_SSAt::nodest &nodes, 
  const local_SSAt::locationt &loc, const local_SSAt::nodet &new_n)
{
  local_SSAt::nodest::iterator it = nodes.find(loc);
  if(it==nodes.end()) //insert
  {
    debug() << "insert new node" << eom;

    nodes[loc] = new_n;
  }
  else //merge nodes
  {
    debug() << "merge node " << eom;

    for(local_SSAt::nodet::equalitiest::const_iterator e_it = new_n.equalities.begin();
	e_it != new_n.equalities.end(); e_it++)
    {
      it->second.equalities.push_back(*e_it);
    }
    for(local_SSAt::nodet::constraintst::const_iterator c_it = new_n.constraints.begin();
	c_it != new_n.constraints.end(); c_it++)
    {
      it->second.constraints.push_back(*c_it);
    }  
  }
}
