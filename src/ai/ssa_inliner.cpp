/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#include <util/i2string.h>

#include "ssa_inliner.h"

/*******************************************************************\

Function: ssa_inlinert::replace()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       summaryt summary)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());

  counter++;

  //equalities for arguments
  summaryt::var_listt::const_iterator it1 = summary.entry_vars.begin();
  for(exprt::operandst::const_iterator it2 = funapp_expr.arguments().begin();
      it2 != funapp_expr.arguments().end(); it2++, it1++)
  {
    assert(it1!=summary.entry_vars.end());
    exprt rhs = *it2; //copy
    rename(rhs);
    new_equs.push_back(equal_exprt(*it1,rhs));
  }

  //constraints for transformer
  node.constraints.push_back(summary.transformer);  //copy
  exprt &transformer = node.constraints.back();
  rename(transformer);
  
  //constraints for return values
  exprt::operandst retvals;
  retvals.reserve(summary.exit_vars.size());
  for(summaryt::var_listt::const_iterator it3 = summary.exit_vars.begin();
      it3 != summary.exit_vars.end(); it3++)
  {
    symbol_exprt rhs = *it3; //copy
    rename(rhs);
    retvals.push_back(equal_exprt(equ_it->lhs(),rhs));
  }
  if(retvals.size()>0) node.constraints.push_back(disjunction(retvals));

  //remove obsolete equalities
  rm_equs.insert(equ_it);
}

/*******************************************************************\

Function: ssa_inlinert::replace()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt::nodest &nodes,
		       local_SSAt::nodet &node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
                       const local_SSAt &function)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());

  counter++;

  //equalities for arguments
  local_SSAt::var_listt::const_iterator it1 = function.entry_vars.begin();
  for(exprt::operandst::const_iterator it2 = funapp_expr.arguments().begin();
      it2 != funapp_expr.arguments().end(); it2++, it1++)
  {
    assert(it1!=function.entry_vars.end());
    exprt rhs = *it2; //copy
    rename(rhs);
    new_equs.push_back(equal_exprt(*it1,rhs));
  }

  //add function body
  for(local_SSAt::nodest::const_iterator n_it = function.nodes.begin();
      n_it != function.nodes.end(); n_it++)
  {
    new_nodes[n_it->first] = n_it->second;  //copy
    local_SSAt::nodet &n = new_nodes[n_it->first];
    for(local_SSAt::nodet::equalitiest::iterator e_it = n.equalities.begin();
	e_it != n.equalities.end(); e_it++)
    {
      rename(*e_it);
    }
    for(local_SSAt::nodet::constraintst::iterator c_it = n.constraints.begin();
	c_it != n.constraints.end(); c_it++)
    {
      rename(*c_it);
    }  
    std::cout << "new node: ";
    new_nodes[n_it->first].output(std::cout,function.ns);
  }
 
  //constraints for return values
  exprt::operandst retvals;
  retvals.reserve(function.exit_vars.size());
  for(summaryt::var_listt::const_iterator it3 = function.exit_vars.begin();
      it3 != function.exit_vars.end(); it3++)
  {
    symbol_exprt rhs = *it3;
    rename(rhs);
    retvals.push_back(equal_exprt(equ_it->lhs(),rhs));
  }
  if(retvals.size()>0) node.constraints.push_back(disjunction(retvals));

  //remove obsolete equalities
  rm_equs.insert(equ_it);
}

/*******************************************************************\

Function: ssa_inlinert::havoc()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::equalitiest::iterator &equ_it)
{
    rm_equs.insert(equ_it);
}

/*******************************************************************\

Function: ssa_inlinert::rename()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename(exprt &expr) 
{
  if(expr.id()==ID_symbol) 
  {
    symbol_exprt &sexpr = to_symbol_expr(expr);
    irep_idt id = id2string(sexpr.get_identifier())+"@"+i2string(counter);
    sexpr.set_identifier(id);
  }
  for(exprt::operandst::iterator it = expr.operands().begin();
      it != expr.operands().end(); it++)
  {
    rename(*it);
  }
}

/*******************************************************************\

Function: ssa_inlinert::commit_node()

  Inputs:

 Outputs:

 Purpose: apply changes to node, must be called after replace and havoc
          (needed because replace and havoc usually called while 
           iterating over equalities,
           and hence we cannot modify them)

\*******************************************************************/

void ssa_inlinert::commit_node(local_SSAt::nodet &node)
{
  //remove obsolete equalities
  for(std::set<local_SSAt::nodet::equalitiest::iterator>::iterator it = rm_equs.begin();
      it != rm_equs.end(); it++) 
  {
    node.equalities.erase(*it);
  }
  rm_equs.clear();
  //insert new equalities
  node.equalities.insert(node.equalities.end(),
    new_equs.begin(),new_equs.end());
  new_equs.clear();
}

void ssa_inlinert::commit_nodes(local_SSAt::nodest &nodes)

{
  //insert new nodes
  nodes.insert(new_nodes.begin(),new_nodes.end());
  new_nodes.clear();
}
