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

void ssa_unwindert::unwind(local_SSAt &SSA, unsigned unwind_max)
{
  // get all backwards edges
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
      local_SSAt::locationt loop_head = i_it->get_target(); 

      for(unsigned unwind=0; unwind<unwind_max; unwind++)
      {
	//TODO: adjust loop_head phis
        for(local_SSAt::locationt it = loop_head;
            it != i_it; it++)
	{
	  local_SSAt::nodest::const_iterator n_it = SSA.nodes.find(it);
          if(n_it==SSA.nodes.end()) continue;
          local_SSAt::nodet n = n_it->second; //copy;
          rename(n,unwind);
          merge_into_nodes(new_nodes,it,n);
        }
      }
    } 
  }
  commit_nodes(SSA.nodes);
}

/*******************************************************************\

Function: ssa_unwindert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_unwindert::rename(exprt &expr, unsigned index) 
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
    rename(*it, index);
  }
}

/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_unwindert::rename(local_SSAt::nodet &node, unsigned index) 
{
  for(local_SSAt::nodet::equalitiest::iterator e_it = node.equalities.begin();
      e_it != node.equalities.end(); e_it++)
  {
    rename(*e_it, index);
  }
  for(local_SSAt::nodet::constraintst::iterator c_it = node.constraints.begin();
      c_it != node.constraints.end(); c_it++)
  {
    rename(*c_it, index);
  }  
}

/*******************************************************************\

Function: ssa_unwindert::commit_nodes()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_unwindert::commit_nodes(local_SSAt::nodest &nodes)
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

Function: ssa_unwindert::merge_node()

  Inputs:

 Outputs:

 Purpose: merges equalities and constraints of two nodes into the first one

\*******************************************************************/

void ssa_unwindert::merge_into_nodes(local_SSAt::nodest &nodes, 
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
