/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#include <util/i2string.h>
#include <util/replace_expr.h>

#include "ssa_inliner.h"
#include "ssa_dereference.h"

/*******************************************************************\

Function: ssa_inlinert::get_summary

  Inputs:

 Outputs:

 Purpose: get summary for function call

\*******************************************************************/

void ssa_inlinert::get_summary(
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const summaryt &summary,
  bool forward,
  exprt::operandst &summaries,
  exprt::operandst &bindings)
{
  counter++;

  // getting globals at call site
  local_SSAt::var_sett cs_globals_in, cs_globals_out;
  goto_programt::const_targett loc=n_it->location;
  if(forward)
  {
    SSA.get_globals(loc, cs_globals_in);
    SSA.get_globals(loc, cs_globals_out, false);
  }
  else
  {
    SSA.get_globals(loc, cs_globals_out);
    SSA.get_globals(loc, cs_globals_in, false);
  }

#if 0
  std::cout << "cs_globals_in: ";
  for(summaryt::var_sett::const_iterator it=cs_globals_in.begin();
      it!=cs_globals_in.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << " ";
  std::cout << std::endl;

  std::cout << "cs_globals_out: ";
  for(summaryt::var_sett::const_iterator it=cs_globals_out.begin();
      it!=cs_globals_out.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << " ";
  std::cout << std::endl;
#endif

  // equalities for arguments
  bindings.push_back(get_replace_params(
    summary.params,
    *f_it,
    summary.globals_in,
    summary.globals_out,
    SSA,
    loc));

  // equalities for globals_in
  if(forward)
    bindings.push_back(
      get_replace_globals_in(summary.globals_in, cs_globals_in));
  else
    bindings.push_back(
      get_replace_globals_in(summary.globals_out, cs_globals_out));

  // constraints for transformer
  exprt transformer;
  if(forward)
    transformer=summary.fw_transformer.is_nil() ? true_exprt() :
      summary.fw_transformer;
  else
  {
    transformer=summary.bw_transformer.is_nil() ? true_exprt() :
      summary.bw_transformer;
  }
  rename(transformer);
  summaries.push_back(
    implies_exprt(SSA.guard_symbol(n_it->location), transformer));

  // equalities for globals out (including unmodified globals)
  if(forward)
    bindings.push_back(
      get_replace_globals_out(
        summary.globals_out,
        cs_globals_in,
        cs_globals_out));
  else
    bindings.push_back(
      get_replace_globals_out(
        summary.globals_in,
        cs_globals_out,
        cs_globals_in));
}

/*******************************************************************\

Function: ssa_inlinert::get_summaries

  Inputs:

 Outputs:

 Purpose: get summary for all function calls

\*******************************************************************/

exprt ssa_inlinert::get_summaries(const local_SSAt &SSA)
{
  exprt::operandst summaries, bindings;
  get_summaries(SSA, true, summaries, bindings);
  return and_exprt(conjunction(bindings), conjunction(summaries));
}

/*******************************************************************\

Function: ssa_inlinert::get_summaries

  Inputs:

 Outputs:

 Purpose: get summary for all function calls

\*******************************************************************/

void ssa_inlinert::get_summaries(
  const local_SSAt &SSA,
  bool forward,
  exprt::operandst &summaries,
  exprt::operandst &bindings)
{
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::const_iterator f_it=
          n_it->function_calls.begin();
        f_it!=n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); // no function pointers
      irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

      if(summary_db.exists(fname))
      {
        get_summary(SSA, n_it, f_it, summary_db.get(fname),
                    forward, summaries, bindings);
      }
    }
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace

  Inputs:

 Outputs:

 Purpose: replaces function calls by summaries
          if available in the summary store
          and does nothing otherwise

\*******************************************************************/

void ssa_inlinert::replace(
  local_SSAt &SSA,
  bool forward,
  bool preconditions_as_assertions)
{
  for(local_SSAt::nodest::iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator
          f_it=n_it->function_calls.begin();
        f_it!=n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); // no function pointers
      irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

      if(summary_db.exists(fname))
      {
        summaryt summary=summary_db.get(fname);

        status() << "Replacing function " << fname << " by summary" << eom;

        // getting globals at call site
        local_SSAt::var_sett cs_globals_in, cs_globals_out;
        goto_programt::const_targett loc=n_it->location;
        SSA.get_globals(loc, cs_globals_in);
        SSA.get_globals(loc, cs_globals_out, false);

        // replace
        replace(
          SSA, n_it, f_it, cs_globals_in, cs_globals_out, summary,
          forward, preconditions_as_assertions);

        // remove function_call
        rm_function_calls.insert(f_it);
      }
      else
        debug() << "No summary available for function " << fname << eom;
      commit_node(n_it);
    }
    commit_nodes(SSA.nodes, n_it);
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

void ssa_inlinert::replace(
  local_SSAt &SSA,
  const ssa_dbt &ssa_db,
  bool recursive, bool rename)
{
  for(local_SSAt::nodest::iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    for(local_SSAt::nodet::function_callst::iterator
          f_it=n_it->function_calls.begin();
        f_it!=n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); // no function pointers
      irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

      if(ssa_db.exists(fname))
      {
        status() << "Inlining function " << fname << eom;
        local_SSAt fSSA=ssa_db.get(fname); // copy

        if(rename)
        {
          // getting globals at call site
          local_SSAt::var_sett cs_globals_in, cs_globals_out;
          goto_programt::const_targett loc=n_it->location;
          SSA.get_globals(loc, cs_globals_in);
          SSA.get_globals(loc, cs_globals_out, false);

          if(recursive)
          {
            replace(fSSA, ssa_db, true);
          }

          // replace
          replace(SSA.nodes, n_it, f_it, cs_globals_in, cs_globals_out, fSSA);
        }
        else // just add to nodes
        {
          for(local_SSAt::nodest::const_iterator fn_it=fSSA.nodes.begin();
              fn_it!=fSSA.nodes.end(); fn_it++)
          {
            debug() << "new node: "; fn_it->output(debug(), fSSA.ns);
            debug() << eom;

            new_nodes.push_back(*fn_it);
          }
        }
      }
      else
        debug() << "No body available for function " << fname << eom;
      commit_node(n_it);
    }
    commit_nodes(SSA.nodes, n_it);
  }
}

/*******************************************************************\

Function: ssa_inlinert::replace

  Inputs:

 Outputs:

 Purpose: inline summary

\*******************************************************************/

void ssa_inlinert::replace(
  local_SSAt &SSA,
  local_SSAt::nodest::iterator node,
  local_SSAt::nodet::function_callst::iterator f_it,
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out,
  const summaryt &summary,
  bool forward,
  bool preconditions_as_assertions)
{
  counter++;

  // equalities for arguments
  replace_params(summary.params, *f_it);

  // equalities for globals_in
  replace_globals_in(summary.globals_in, cs_globals_in);

  // constraints for precondition and transformer
  exprt precondition;
  if(forward)
    precondition=summary.fw_precondition;
  else
    precondition=summary.bw_precondition;
  if(!preconditions_as_assertions)
  {
    rename(precondition);
    node->constraints.push_back(
      implies_exprt(SSA.guard_symbol(node->location),
                    precondition));
  }
  else
  {
    rename(precondition);
    node->assertions.push_back(
      implies_exprt(SSA.guard_symbol(node->location),
                    precondition));
  }
  exprt transformer;
  if(forward)
    transformer=summary.fw_transformer;
  else
    transformer=summary.bw_transformer;
  node->constraints.push_back(transformer);  // copy
  exprt &_transformer=node->constraints.back();
  rename(_transformer);

  // remove function call
  rm_function_calls.insert(f_it);

  // equalities for globals out (including unmodified globals)
  replace_globals_out(summary.globals_out, cs_globals_in, cs_globals_out);
}

/*******************************************************************\

 Function: ssa_inlinert::replace

 Inputs:

 Outputs:

 Purpose: inline function

 Remark: local_SSAt::nodest maps a goto program target to a single SSA node,
         when inlining several calls to the same function
         instructions appear factorized by the goto program targets

\*******************************************************************/

void ssa_inlinert::replace(
  local_SSAt::nodest &nodes,
  local_SSAt::nodest::iterator node,
  local_SSAt::nodet::function_callst::iterator f_it,
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out,
  const local_SSAt &function)
{
  counter++;

  // equalities for arguments
  replace_params(function.params, *f_it);

  // equalities for globals_in
  replace_globals_in(function.globals_in, cs_globals_in);

  // add function body
  for(local_SSAt::nodest::const_iterator n_it=function.nodes.begin();
      n_it!=function.nodes.end(); n_it++)
  {
    local_SSAt::nodet n=*n_it;  // copy
    rename(n);
    new_nodes.push_back(n);
  }

  // remove function call
  rm_function_calls.insert(f_it);

  // equalities for globals out (including unmodified globals)
  replace_globals_out(function.globals_out, cs_globals_in, cs_globals_out);
}

/*******************************************************************\

Function: ssa_inlinert::get_replace_globals_in

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt ssa_inlinert::get_replace_globals_in(
  const local_SSAt::var_sett &globals_in,
  const local_SSAt::var_sett &globals)
{
  // equalities for globals_in
  exprt::operandst c;
  for(summaryt::var_sett::const_iterator it=globals_in.begin();
      it!=globals_in.end(); it++)
  {
    symbol_exprt lhs=*it; // copy
    rename(lhs);
    symbol_exprt rhs;
    if(find_corresponding_symbol(*it, globals, rhs))
    {
      debug() << "binding: " << lhs.get_identifier() << "=="
              << rhs.get_identifier() << eom;
      c.push_back(equal_exprt(lhs, rhs));
    }
#if 0
    else
      warning() << "'" << it->get_identifier()
                << "' not bound in caller" << eom;
#endif
  }
  return conjunction(c);
}

/*******************************************************************\

Function: ssa_inlinert::replace_globals_in

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_globals_in(
  const local_SSAt::var_sett &globals_in,
  const local_SSAt::var_sett &globals)
{
  // equalities for globals_in
  for(summaryt::var_sett::const_iterator it=globals_in.begin();
      it!=globals_in.end(); it++)
  {
    symbol_exprt lhs=*it; // copy
    rename(lhs);
    symbol_exprt rhs;
    if(find_corresponding_symbol(*it, globals, rhs))
    {
      debug() << "binding: " << lhs.get_identifier() << "=="
              << rhs.get_identifier() << eom;
      new_equs.push_back(equal_exprt(lhs, rhs));
    }
#if 0
    else
      warning() << "'" << it->get_identifier()
                << "' not bound in caller" << eom;
#endif
  }
}

/*******************************************************************\

Function: ssa_inlinert::get_replace_params

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt ssa_inlinert::get_replace_params(
  const local_SSAt::var_listt &params,
  const function_application_exprt &funapp_expr,
  const local_SSAt::var_sett &globals_in,
  const local_SSAt::var_sett &globals_out,
  const local_SSAt &SSA,
  const local_SSAt::locationt &loc)
{
  // equalities for arguments
  exprt::operandst c;
  local_SSAt::var_listt::const_iterator p_it=params.begin();
  for(exprt::operandst::const_iterator it=funapp_expr.arguments().begin();
      it!=funapp_expr.arguments().end(); it++, p_it++)
  {
    local_SSAt::var_listt::const_iterator next_p_it=p_it;
    if(funapp_expr.arguments().size()!=params.size() &&
       ++next_p_it==params.end()) // TODO: handle ellipsis
    {
      warning() << "ignoring excess function arguments" << eom;
      break;
    }

    exprt lhs=*p_it; // copy
    rename(lhs);
    c.push_back(equal_exprt(lhs, *it));

    // For pointer parameters create equalities between pointed object passed as global and
    // corresponding object in caller
    if (p_it->type().id() == ID_pointer) {
      // Find corresponding objects in caller's objects (separately for entry and exit)
      exprt pointed_ssa_sym_in;
      exprt pointed_ssa_sym_out;
      for (equal_exprt equal : SSA.find_node(loc)->equalities)
      { // search through equalities with argument value
        if (equal.rhs().id() == ID_symbol &&
            to_symbol_expr(equal.rhs()).get_identifier() == to_symbol_expr(*it).get_identifier())
        {
          exprt arg_pointed = dereference(equal.lhs(), SSA.ssa_value_ai[loc], "", SSA.ns);
          if (arg_pointed.id() == ID_address_of)
          {
            arg_pointed = to_address_of_expr(arg_pointed).object();
          }
          ssa_objectt pointed_ssa_obj(arg_pointed, SSA.ns);
          // get correct SSA symbol for function call entry
          pointed_ssa_sym_in = SSA.name(pointed_ssa_obj, local_SSAt::OUT,
                                        SSA.get_def_loc(to_symbol_expr(arg_pointed), loc));
          // get correct SSA symbol for function call exit
          pointed_ssa_sym_out = SSA.name(pointed_ssa_obj, local_SSAt::OUT, loc);
        }
      }

      // Find globals containing pointed object and create equalities
      irep_idt global_id = id2string(to_symbol_expr(*p_it).get_identifier())+"'obj";
      symbol_exprt expr_to_find(global_id, p_it->type().subtype());

      // Entry global
      symbol_exprt global_in;
      if(find_corresponding_symbol(expr_to_find,globals_in,global_in)) {
        rename(global_in);
        c.push_back(equal_exprt(global_in,pointed_ssa_sym_in));
      }
      // Exit global
      symbol_exprt global_out;
      if(find_corresponding_symbol(expr_to_find,globals_out,global_out)) {
        rename(global_out);
        c.push_back(equal_exprt(global_out, pointed_ssa_sym_out));
      }
    }
  }
  return conjunction(c);
}

/*******************************************************************\

Function: ssa_inlinert::replace_params

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::replace_params(
  const local_SSAt::var_listt &params,
  const function_application_exprt &funapp_expr)
{
  // equalities for arguments
  local_SSAt::var_listt::const_iterator p_it=params.begin();
  for(exprt::operandst::const_iterator it=funapp_expr.arguments().begin();
      it!=funapp_expr.arguments().end(); it++, p_it++)
  {
    local_SSAt::var_listt::const_iterator next_p_it=p_it;
    if(funapp_expr.arguments().size()!=params.size() &&
       ++next_p_it==params.end()) // TODO: handle ellipsis
    {
      warning() << "ignoring excess function arguments" << eom;
      break;
    }

    exprt lhs=*p_it; // copy
    rename(lhs);
    new_equs.push_back(equal_exprt(lhs, *it));
  }
}

/*******************************************************************\

Function: ssa_inlinert::get_replace_globals_out

  Inputs:

 Outputs:

 Purpose: equalities for globals out (including unmodified globals)

\*******************************************************************/

exprt ssa_inlinert::get_replace_globals_out(
  const local_SSAt::var_sett &globals_out,
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out)
{
  // equalities for globals_out
  exprt::operandst c;
  for(summaryt::var_sett::const_iterator it=cs_globals_out.begin();
      it!=cs_globals_out.end(); it++)
  {
    symbol_exprt rhs=*it; // copy
    symbol_exprt lhs;
    if(find_corresponding_symbol(*it, globals_out, lhs))
      rename(lhs);
    else
      assert(find_corresponding_symbol(*it, cs_globals_in, lhs));
    c.push_back(equal_exprt(lhs, rhs));
  }
  return conjunction (c);
}

/*******************************************************************\

Function: ssa_inlinert::replace_globals_out

  Inputs:

 Outputs:

 Purpose: equalities for globals out (including unmodified globals)

\*******************************************************************/

void ssa_inlinert::replace_globals_out(
  const local_SSAt::var_sett &globals_out,
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out)
{
  // equalities for globals_out
  for(summaryt::var_sett::const_iterator it=cs_globals_out.begin();
      it!=cs_globals_out.end(); it++)
  {
    symbol_exprt rhs=*it; // copy
    symbol_exprt lhs;
    if(find_corresponding_symbol(*it, globals_out, lhs))
      rename(lhs);
    else
      assert(find_corresponding_symbol(*it, cs_globals_in, lhs));
    new_equs.push_back(equal_exprt(lhs, rhs));
  }
}

/*******************************************************************\

Function: ssa_inlinert::havoc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::havoc(
  local_SSAt::nodet &node,
  local_SSAt::nodet::function_callst::iterator f_it)
{
  // remove function call
  rm_function_calls.insert(f_it);
}

/*******************************************************************\

Function: ssa_inlinert::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &sexpr=to_symbol_expr(expr);
    irep_idt id=id2string(sexpr.get_identifier())+"@"+i2string(counter);
    sexpr.set_identifier(id);
  }
  Forall_operands(op, expr)
    rename(*op);
}

/*******************************************************************\

Function: ssa_inlinert::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename(local_SSAt::nodet &node)
{
  for(auto &e : node.equalities)
    rename(e);
  for(auto &c : node.constraints)
    rename(c);
  for(auto &a : node.assertions)
    rename(a);
  for(auto &f : node.function_calls)
    rename(f);
}

/*******************************************************************\

Function: ssa_inlinert::rename_to_caller

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename_to_caller(
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const local_SSAt::var_listt &params,
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &globals_in,
  exprt &expr)
{
  assert(params.size()==f_it->arguments().size());

  replace_mapt replace_map;

  local_SSAt::var_listt::const_iterator p_it=params.begin();
  for(exprt::operandst::const_iterator it=f_it->arguments().begin();
      it!=f_it->arguments().end(); ++it, ++p_it)
  {
    local_SSAt::var_listt::const_iterator next_p_it=p_it;
    if(f_it->arguments().size()!=params.size() &&
       ++next_p_it==params.end()) // TODO: handle ellipsis
    {
      warning() << "ignoring excess function arguments" << eom;
      break;
    }
    replace_map[*p_it]=*it;
  }

  for(summaryt::var_sett::const_iterator it=globals_in.begin();
      it!=globals_in.end(); it++)
  {
    symbol_exprt cg;
    if(find_corresponding_symbol(*it, cs_globals_in, cg))
      replace_map[*it]=cg;
    else
    {
#if 0
      warning() << "'" << it->get_identifier()
                << "' not bound in caller" << eom;
#endif
      replace_map[*it]=
        symbol_exprt(
          id2string(it->get_identifier())+"@"+i2string(++counter), it->type());
    }
  }

  replace_expr(replace_map, expr);
}

/*******************************************************************\

Function: ssa_inlinert::rename_to_callee

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_inlinert::rename_to_callee(
  local_SSAt::nodet::function_callst::const_iterator f_it,
  const local_SSAt::var_listt &params,
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &globals_in,
  exprt &expr)
{
  replace_mapt replace_map;

  local_SSAt::var_listt::const_iterator p_it=params.begin();
  for(exprt::operandst::const_iterator it=f_it->arguments().begin();
      it!=f_it->arguments().end(); ++it, ++p_it)
  {
    local_SSAt::var_listt::const_iterator next_p_it=p_it;
    if(f_it->arguments().size()!=params.size() &&
       ++next_p_it==params.end()) // TODO: handle ellipsis
    {
      warning() << "ignoring excess function arguments" << eom;
      break;
    }
    replace_map[*it]=*p_it;
  }

  for(summaryt::var_sett::const_iterator it=cs_globals_in.begin();
      it!=cs_globals_in.end(); it++)
  {
    symbol_exprt cg;
    if(find_corresponding_symbol(*it, globals_in, cg))
      replace_map[*it]=cg;
    else
    {
#if 0
      warning() << "'" << it->get_identifier()
                << "' not bound in caller" << eom;
#endif
      replace_map[*it]=
        symbol_exprt(
          id2string(it->get_identifier())+"@"+i2string(++counter), it->type());
    }
  }

  replace_expr(replace_map, expr);
}

/*******************************************************************\

Function: ssa_inlinert::commit_node

  Inputs:

 Outputs:

 Purpose: apply changes to node, must be called after replace and havoc
          (needed because replace and havoc usually called while
           iterating over equalities,
           and hence we cannot modify them)

\*******************************************************************/

void ssa_inlinert::commit_node(local_SSAt::nodest::iterator node)
{
  // remove obsolete function calls
  for(std::set<local_SSAt::nodet::function_callst::iterator>::iterator
        it=rm_function_calls.begin();
      it!=rm_function_calls.end(); it++)
  {
    node->function_calls.erase(*it);
  }
  rm_function_calls.clear();

  // insert new equalities
  node->equalities.insert(
    node->equalities.end(), new_equs.begin(), new_equs.end());
  new_equs.clear();
}

/*******************************************************************\

Function: ssa_inlinert::commit_nodes

  Inputs:

 Outputs:

 Purpose: returns true if no nodes were to be committed

\*******************************************************************/

bool ssa_inlinert::commit_nodes(
  local_SSAt::nodest &nodes,
  local_SSAt::nodest::iterator n_pos)
{
  if(new_nodes.empty())
    return true;
  nodes.splice(n_pos, new_nodes, new_nodes.begin(), new_nodes.end());
  return false;
}

/*******************************************************************\

Function: ssa_inlinert::find_corresponding_symbol

  Inputs:

 Outputs: returns false if the symbol is not found

 Purpose:

\*******************************************************************/

bool ssa_inlinert::find_corresponding_symbol(
  const symbol_exprt &s,
  const local_SSAt::var_sett &globals,
  symbol_exprt &s_found)
{
  const irep_idt &s_orig_id=get_original_identifier(s);
  for(local_SSAt::var_sett::const_iterator it=globals.begin();
      it!=globals.end(); it++)
  {
#if 0
    std::cout << s_orig_id << "=?= "
              << get_original_identifier(*it) << std::endl;
#endif
    if(s_orig_id==get_original_identifier(*it))
    {
      s_found=*it;
      return true;
    }
  }
  return false;
}

/*******************************************************************\

Function: ssa_inlinert::get_original_identifier

  Inputs:

 Outputs:

 Purpose: TODO: this is a potential source of bugs. Better way to do that?

\*******************************************************************/

irep_idt ssa_inlinert::get_original_identifier(const symbol_exprt &s)
{
  std::string id=id2string(s.get_identifier());

  // find first #@%!$ where afterwards there are no letters
  size_t pos=std::string::npos;
  for(size_t i=0; i<id.size(); ++i)
  {
    char c=id.at(i);
    if(pos==std::string::npos)
    {
      if(c=='#' || c=='@' || c=='%' || c=='!' || c=='$')
        pos=i;
    }
    else
    {
      if(!(c=='#' || c=='@' || c=='%' || c=='!' || c=='$') &&
         !(c=='p' || c=='h' || c=='i') &&
         !('0'<=c && c<='9'))
        pos=std::string::npos;
    }
  }
  if(pos!=std::string::npos)
    id=id.substr(0, pos);
  return id;
}

