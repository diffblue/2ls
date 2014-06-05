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

void ssa_inlinert::replace(local_SSAt::nodest &nodes,
                       local_SSAt::nodest::iterator node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
		       const local_SSAt::var_sett &globals, //names of globals at call site
                       const summaryt &summary)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());

  counter++;

  //equalities for arguments
  replace_params(summary.params,funapp_expr);

  //equalities for globals_in
  replace_globals_in(summary.globals_in,globals);

  //constraints for transformer
  node->second.constraints.push_back(summary.transformer);  //copy
  exprt &transformer = node->second.constraints.back();
  rename(transformer);
  
  //constraints for return values
  replace_return_values(node,equ_it,summary.returns);

  //remove obsolete equalities
  rm_equs.insert(equ_it);

  //rename "globals_out in caller" to globals_out in caller
  replace_globals_out(nodes,node,summary.globals_out);
}

/*******************************************************************\

Function: ssa_inlinert::replace()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt::nodest &nodes,
                       local_SSAt::nodest::iterator node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
		       const local_SSAt::var_sett &globals, //names of globals at call site
                       const local_SSAt &function)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());

  counter++;

  //equalities for arguments
  replace_params(function.params,funapp_expr);

  //equalities for globals_in
  replace_globals_in(function.globals_in,globals);

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
  replace_return_values(node,equ_it,function.returns);

  //remove obsolete equalities
  rm_equs.insert(equ_it);

  //rename "globals_out in caller" to globals_out in caller
  replace_globals_out(nodes,node,function.globals_out);
}

/*******************************************************************\

Function: ssa_inlinert::replace_globals_in()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_globals_in(const local_SSAt::var_sett &globals_in, 
  const local_SSAt::var_sett &globals)
{
  //equalities for globals_in
  for(summaryt::var_sett::const_iterator it = globals_in.begin();
      it != globals_in.end(); it++)
  {
    symbol_exprt lhs = *it; //copy
    rename(lhs);
    symbol_exprt rhs;
    assert(find_corresponding_symbol(*it,globals,rhs));
    new_equs.push_back(equal_exprt(lhs,rhs));
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace_params()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_params(const local_SSAt::var_listt &params,
  const function_application_exprt &funapp_expr)
{
  //equalities for arguments
  local_SSAt::var_listt::const_iterator p_it = params.begin();
  for(exprt::operandst::const_iterator it = funapp_expr.arguments().begin();
      it != funapp_expr.arguments().end(); it++, p_it++)
  {
    assert(p_it!=params.end());
    exprt lhs = *p_it; //copy
    rename(lhs);
    new_equs.push_back(equal_exprt(lhs,*it));
  }
}


/*******************************************************************\

Function: ssa_inlinert::replace_return_values()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_return_values(local_SSAt::nodest::iterator node, 
					 local_SSAt::nodet::equalitiest::iterator equ_it,
					 const local_SSAt::var_sett &returns)
{
  //constraints for return values
  exprt::operandst retvals;
  retvals.reserve(returns.size());
  for(summaryt::var_sett::const_iterator it = returns.begin();
      it != returns.end(); it++)
  {
    symbol_exprt rhs = *it;
    rename(rhs);
    retvals.push_back(equal_exprt(equ_it->lhs(),rhs));
  }
  if(retvals.size()>0) node->second.constraints.push_back(disjunction(retvals));
}

/*******************************************************************\

Function: ssa_inlinert::replace_globals_out()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_globals_out(local_SSAt::nodest &nodes,
				       local_SSAt::nodest::iterator node,
                                       const local_SSAt::var_sett &globals_out)
{
  //rename "globals_out in caller" to globals_out in caller
  for(node++; node != nodes.end(); node++)
  {
    for(local_SSAt::nodet::equalitiest::iterator it = node->second.equalities.begin();
        it != node->second.equalities.end(); it++)
    {
      rename_globals(it->rhs(),globals_out);
    }
    for(local_SSAt::nodet::constraintst::iterator it = node->second.constraints.begin();
        it != node->second.constraints.end(); it++)
    {
      rename_globals(*it,globals_out);
    }  
  }
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

Function: ssa_inlinert::rename_globals

  Inputs:

 Outputs:

 Purpose: replace globals in expr by corresponding variable in globals

\*******************************************************************/

void ssa_inlinert::rename_globals(exprt &expr, const local_SSAt::var_sett &globals) 
{
  if(expr.id()==ID_symbol) 
  {
    symbol_exprt &s = to_symbol_expr(expr);
    //for each occurrence 
    symbol_exprt s_new;
    if(find_corresponding_symbol(s,globals,s_new))
    {
      rename(s_new);
      std::cout << "replace global " << s.get_identifier() << " by modified global " << 
        s_new.get_identifier() << std::endl;
      s.set_identifier(s_new.get_identifier());
    }
  }
  for(exprt::operandst::iterator it = expr.operands().begin();
      it != expr.operands().end(); it++)
  {
    rename_globals(*it,globals);
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

void ssa_inlinert::commit_node(local_SSAt::nodest::iterator node)
{
  //remove obsolete equalities
  for(std::set<local_SSAt::nodet::equalitiest::iterator>::iterator it = rm_equs.begin();
      it != rm_equs.end(); it++) 
  {
    node->second.equalities.erase(*it);
  }
  rm_equs.clear();
  //insert new equalities
  node->second.equalities.insert(node->second.equalities.end(),
    new_equs.begin(),new_equs.end());
  new_equs.clear();
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
  nodes.insert(new_nodes.begin(),new_nodes.end());
  new_nodes.clear();
}

/*******************************************************************\

Function: ssa_inlinert::find_corresponding_symbol

  Inputs:

 Outputs: returns false if the symbol is not found

 Purpose:

\*******************************************************************/

bool ssa_inlinert::find_corresponding_symbol(const symbol_exprt &s, 
					 const local_SSAt::var_sett &globals,
                                         symbol_exprt &s_found)
{
  for(local_SSAt::var_sett::const_iterator it = globals.begin();
      it != globals.end(); it++)
  {
    if(get_original_identifier(s)==get_original_identifier(*it))
    {
      s_found = *it;
      return true;
    }
  }
  return false;
}

/*******************************************************************\

Function: ssa_inlinert::get_original_identifier

  Inputs:

 Outputs: 

 Purpose: TODO: better way to do that?

\*******************************************************************/

irep_idt ssa_inlinert::get_original_identifier(const symbol_exprt &s)
{
  std::string id = id2string(s.get_identifier());
  size_t pos = id.find("#");
  if(pos==std::string::npos) pos = id.find("@");
  if(pos!=std::string::npos) id = id.substr(0,pos);
  return id;
}
