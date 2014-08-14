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

  for(local_SSAt::nodest::iterator n_it = SSA.nodes.begin(); 
      n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead == SSA.nodes.end()) continue;
    //we've found a loop

    local_SSAt::locationt loop_head = n_it->loophead->location; 

    std::cout << "loop head: " << std::endl;
    n_it->loophead->output(std::cout,SSA.ns);

    // get variables at beginning and end of loop body
    std::map<exprt, exprt> pre_post_exprs;

    const ssa_domaint::phi_nodest &phi_nodes =
      SSA.ssa_analysis[loop_head].phi_nodes;

    for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
	o_it!=SSA.ssa_objects.objects.end();
	o_it++)
    {
      ssa_domaint::phi_nodest::const_iterator p_it =
	phi_nodes.find(o_it->get_identifier());

      if(p_it==phi_nodes.end()) continue; // object not modified in this loop

      symbol_exprt pre = 
	SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
      symbol_exprt post = SSA.read_rhs(*o_it, n_it->location);

      pre_post_exprs[pre] = post;
    }

    // unwind that loop
    for(unsigned unwind=unwind_max; unwind>0; unwind--)
    {
      // insert loop_head
      local_SSAt::nodet node = *n_it->loophead; //copy
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
      new_nodes.push_back(node);

      // insert body
      local_SSAt::nodest::iterator it = n_it->loophead; it++;
      for(;it != n_it; it++)
      {
	local_SSAt::nodet n = *it; //copy;
	rename(n,unwind);
	new_nodes.push_back(n);
      }
    }

    // feed last unwinding into original loop_head, modified in place
    for(local_SSAt::nodet::equalitiest::iterator 
          e_it = n_it->loophead->equalities.begin();
	e_it != n_it->loophead->equalities.end(); e_it++)
    {
      if(e_it->rhs().id()!=ID_if) continue;
        
      if_exprt &e = to_if_expr(e_it->rhs());
      e.false_case() = pre_post_exprs[e.true_case()];
      rename(e.false_case(),1);
    }
    commit_nodes(SSA.nodes,n_it->loophead); //apply changes

#if 0
    std::cout << "SSA after loop: " << std::endl;
    SSA.output(std::cout);
#endif
  }
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

void ssa_unwindert::commit_nodes(local_SSAt::nodest &nodes,
                                 local_SSAt::nodest::iterator n_pos)
{
  nodes.splice(n_pos,new_nodes,new_nodes.begin(),new_nodes.end());
}

