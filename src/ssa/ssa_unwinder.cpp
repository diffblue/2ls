/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

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
  if(unwind_max==0) return; 

  // TODO: currently does not work for nested loops!

  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto()) //we've found a loop
    {
      local_SSAt::locationt loop_head = i_it->get_target(); 
      //      const irep_idt loop_id=goto_programt::loop_id(i_it);

      // get variables at beginning and end of loop body
      std::map<exprt, exprt> pre_post_exprs;

      const ssa_domaint::phi_nodest &phi_nodes =
        SSA.ssa_analysis[i_it->get_target()].phi_nodes;

      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::phi_nodest::const_iterator p_it =
        phi_nodes.find(o_it->get_identifier());

        if(p_it==phi_nodes.end()) continue; // object not modified in this loop

        symbol_exprt pre = SSA.name(*o_it, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt post = SSA.read_rhs(*o_it, i_it);

        pre_post_exprs[pre] = post;
      }

       // unwind that loop
      for(unsigned unwind=unwind_max; unwind>0; unwind--)
      {
	// insert loop_head
        local_SSAt::nodet node = SSA.nodes[loop_head]; //copy
	for(local_SSAt::nodet::equalitiest::iterator 
            e_it = node.equalities.begin();
	    e_it != node.equalities.end(); e_it++)
	{
	  if(e_it->rhs().id()!=ID_if) 
	  {
            rename(*e_it,unwind);
            continue;
	  }

          if_exprt &e = to_if_expr(e_it->rhs());
         
          if(unwind==unwind_max)
	  {
	    rename(e_it->lhs(),unwind);
            e_it->rhs() = e.false_case();
	  }
          else
	  {
	    e_it->rhs() = pre_post_exprs[e.true_case()];
	    rename(e_it->rhs(),unwind+1);
	    rename(e_it->lhs(),unwind);
	  }
	}
        merge_into_nodes(new_nodes,loop_head,node);

        // insert body
        local_SSAt::locationt it = loop_head; it++;
        for(;it != i_it; it++)
	{
	  local_SSAt::nodest::const_iterator n_it = SSA.nodes.find(it);
          if(n_it==SSA.nodes.end()) continue;

          local_SSAt::nodet n = n_it->second; //copy;
          rename(n,unwind);
          merge_into_nodes(new_nodes,it,n);
        }
      }

      // feed last unwinding into original loop_head
      local_SSAt::nodet &node = SSA.nodes[loop_head]; //modify in place
      for(local_SSAt::nodet::equalitiest::iterator 
          e_it = node.equalities.begin();
          e_it != node.equalities.end(); e_it++)
      {
        if(e_it->rhs().id()!=ID_if) continue;
        
        if_exprt &e = to_if_expr(e_it->rhs());
        e.false_case() = pre_post_exprs[e.true_case()];
        rename(e.false_case(),1);
      }
    } 
  }
  commit_nodes(SSA.nodes); //apply changes
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
  for(local_SSAt::nodet::assertionst::iterator a_it = node.assertions.begin();
      a_it != node.assertions.end(); a_it++)
  {
    rename(*a_it, index);
  }  
  for(local_SSAt::nodet::function_callst::iterator 
      f_it = node.function_calls.begin();
      f_it != node.function_calls.end(); f_it++)
  {
    rename(*f_it, index);
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

    for(local_SSAt::nodet::equalitiest::const_iterator 
        e_it = new_n.equalities.begin();
	e_it != new_n.equalities.end(); e_it++)
    {
      it->second.equalities.push_back(*e_it);
    }
    for(local_SSAt::nodet::constraintst::const_iterator 
        c_it = new_n.constraints.begin();
	c_it != new_n.constraints.end(); c_it++)
    {
      it->second.constraints.push_back(*c_it);
    }  
    for(local_SSAt::nodet::assertionst::const_iterator 
        a_it = new_n.assertions.begin();
	a_it != new_n.assertions.end(); a_it++)
    {
      it->second.assertions.push_back(*a_it);
    }  
    for(local_SSAt::nodet::function_callst::const_iterator 
        f_it = new_n.function_calls.begin();
	f_it != new_n.function_calls.end(); f_it++)
    {
      it->second.function_calls.push_back(*f_it);
    }  
  }
}
