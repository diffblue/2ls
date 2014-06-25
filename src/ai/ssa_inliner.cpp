/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#include <util/i2string.h>

#include "ssa_inliner.h"

/*******************************************************************\

Function: ssa_inlinert::replace

  Inputs:

 Outputs: 

 Purpose: replaces function calls by summaries
          if available in the summary store
          and does nothing otherwise

\*******************************************************************/


void ssa_inlinert::replace(local_SSAt &SSA,
	     const summary_storet &summary_store)
{
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); n!=SSA.nodes.end(); n++)
  {
    for(local_SSAt::nodet::equalitiest::iterator e = n->second.equalities.begin();
        e != n->second.equalities.end(); e++)
    {
      if(e->rhs().id() != ID_function_application) continue;

      function_application_exprt f = to_function_application_expr(e->rhs());
      assert(f.function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f.function()).get_identifier();

      if(summary_store.exists(fname)) 
      {
        summaryt summary = summary_store.get(fname);

        status() << "Replacing function " << fname << " by summary" << eom;

	//getting globals at call site
	local_SSAt::var_sett cs_globals_in, cs_globals_out; 
	goto_programt::const_targett loc = n->first;
	SSA.get_globals(loc,cs_globals_in);
	assert(loc!=SSA.goto_function.body.instructions.end());
	SSA.get_globals(++loc,cs_globals_out);

        //replace
        replace(SSA.nodes,n,e,cs_globals_in,cs_globals_out,summary);
      }
      else debug() << "No summary available for function " << fname << eom;
      commit_node(n);
    }
    commit_nodes(SSA.nodes);
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace

  Inputs:

 Outputs: 

 Purpose: replaces inlines functions 
          if SSA is available in functions
          and does nothing otherwise

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt &SSA,
               const std::map<irep_idt, local_SSAt*> &functions, 
	       bool recursive, bool rename)
{
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); n!=SSA.nodes.end(); n++)
  {
    for(local_SSAt::nodet::equalitiest::iterator e = n->second.equalities.begin();
        e != n->second.equalities.end(); e++)
    {
      if(e->rhs().id() != ID_function_application) continue;

      function_application_exprt f = to_function_application_expr(e->rhs());
      assert(f.function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f.function()).get_identifier();

      if(functions.find(fname)!=functions.end()) 
      {
        status() << "Inlining function " << fname << eom;
        local_SSAt fSSA = *functions.at(fname); //copy

        if(rename)
        {
	  //getting globals at call site
	  local_SSAt::var_sett cs_globals_in, cs_globals_out; 
	  goto_programt::const_targett loc = n->first;
	  SSA.get_globals(loc,cs_globals_in);
	  assert(loc!=SSA.goto_function.body.instructions.end());
	  SSA.get_globals(++loc,cs_globals_out);

	  if(recursive)
	    {
	      replace(fSSA,functions,true);
	    }

	  //replace
	  replace(SSA.nodes,n,e,cs_globals_in,cs_globals_out,fSSA);
        }
        else // just add to nodes
	{
	  for(local_SSAt::nodest::const_iterator n_it = fSSA.nodes.begin();
	      n_it != fSSA.nodes.end(); n_it++)
	  {
            debug() << "new node: "; n_it->second.output(debug(),fSSA.ns); debug() << eom;

	    merge_into_nodes(new_nodes,n_it->first,n_it->second);
	  }
	}
      }
      else debug() << "No body available for function " << fname << eom;
      commit_node(n);
    }
    commit_nodes(SSA.nodes);
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace()

  Inputs:

 Outputs:

 Purpose: inline summary

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt::nodest &nodes,
                       local_SSAt::nodest::iterator node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
		       const local_SSAt::var_sett &cs_globals_in,
		       const local_SSAt::var_sett &cs_globals_out, 
                       const summaryt &summary)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());

  counter++;

  //equalities for arguments
  replace_params(summary.params,funapp_expr);

  //equalities for globals_in
  replace_globals_in(summary.globals_in,cs_globals_in);

  //constraints for transformer
  node->second.constraints.push_back(summary.transformer);  //copy
  exprt &transformer = node->second.constraints.back();
  rename(transformer);
  
  //remove obsolete equalities
  rm_equs.insert(equ_it);

  //equalities for globals out (including unmodified globals)
  replace_globals_out(summary.globals_out,cs_globals_in,cs_globals_out);
}

/*******************************************************************\

 Function: ssa_inlinert::replace()

 Inputs:

 Outputs:

 Purpose: inline function 

 Remark: local_SSAt::nodest maps a goto program target to a single SSA node,
         when inlining several calls to the same function 
         instructions appear factorized by the goto program targets 

\*******************************************************************/

void ssa_inlinert::replace(local_SSAt::nodest &nodes,
                       local_SSAt::nodest::iterator node, 
                       local_SSAt::nodet::equalitiest::iterator equ_it, 
		       const local_SSAt::var_sett &cs_globals_in,
		       const local_SSAt::var_sett &cs_globals_out, 
                       const local_SSAt &function)
{
  function_application_exprt funapp_expr = to_function_application_expr(equ_it->rhs());

  counter++;

  //equalities for arguments
  replace_params(function.params,funapp_expr);

  //equalities for globals_in
  replace_globals_in(function.globals_in,cs_globals_in);

  //add function body
  for(local_SSAt::nodest::const_iterator n_it = function.nodes.begin();
      n_it != function.nodes.end(); n_it++)
  {
    local_SSAt::nodet n = n_it->second;  //copy
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
    merge_into_nodes(new_nodes,n_it->first,n);
  }
 
  //remove obsolete equalities
  rm_equs.insert(equ_it);

  //equalities for globals out (including unmodified globals)
  replace_globals_out(function.globals_out,cs_globals_in,cs_globals_out);
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

Function: ssa_inlinert::replace_globals_out()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_globals_out(const local_SSAt::var_sett &globals_out, 
				       const local_SSAt::var_sett &cs_globals_in,  
				       const local_SSAt::var_sett &cs_globals_out)
{

  //equalities for globals_out
  for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
      it != cs_globals_out.end(); it++)
  {
    symbol_exprt rhs = *it; //copy
    symbol_exprt lhs;
    if(find_corresponding_symbol(*it,globals_out,lhs))
      rename(lhs);
    else
      assert(find_corresponding_symbol(*it,cs_globals_in,lhs));
    new_equs.push_back(equal_exprt(lhs,rhs));
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

