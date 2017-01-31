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

  //equalities for arguments
  bindings.push_back(get_replace_params(
    summary.params,
    *f_it,
    cs_globals_in,
    cs_globals_out,
    SSA,
    summary,
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
  summaries.push_back(implies_exprt(
    SSA.guard_symbol(n_it->location), transformer));
  
  // equalities for globals out (including unmodified globals)
  if(forward)
    bindings.push_back(get_replace_globals_out(
      cs_globals_in, cs_globals_out, summary, *f_it, SSA, loc));
  else
    bindings.push_back(get_replace_globals_out(
      cs_globals_out, cs_globals_in, summary, *f_it, SSA, loc));
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
    // bind only real globals - filter out heap objects
    if(id2string(it->get_identifier()).find("'obj")==std::string::npos)
    {
      symbol_exprt lhs=*it; // copy
      rename(lhs);
      symbol_exprt rhs;
      if(find_corresponding_symbol(*it, globals, rhs))
      {
        debug() << "binding: " << lhs.get_identifier() << " == "
                << rhs.get_identifier() << eom;
        c.push_back(equal_exprt(lhs, rhs));
      }
#if 0
      else
        warning() << "'" << it->get_identifier()
                  << "' not bound in caller" << eom;
#endif
    }
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
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out,
  const local_SSAt &SSA,
  const summaryt &summary,
  const local_SSAt::locationt &loc)
{
  // equalities for arguments
  exprt::operandst c;
  local_SSAt::var_listt::const_iterator p_it=params.begin();
  for(exprt::operandst::const_iterator it=funapp_expr.arguments().begin();
      it!=funapp_expr.arguments().end(); it++, p_it++)
  {
    local_SSAt::var_listt::const_iterator next_p_it=p_it;
    if (funapp_expr.arguments().size()!=params.size() &&
        ++next_p_it==params.end()) // TODO: handle ellipsis
    {
      warning() << "ignoring excess function arguments" << eom;
      break;
    }

    exprt param=*p_it; // copy
    exprt arg=*it; // copy

    exprt lhs=param;
    rename(lhs);
    // bind parameter <-> argument
    c.push_back(equal_exprt(lhs, arg));

    typet arg_type=SSA.ns.follow(arg.type());

    // Bind objects pointed by parameter/argument pair
    std::list<exprt> args_in={arg};
    std::list<exprt> args_out={arg};
    std::list<exprt> params_in={param};
    std::list<exprt> params_out={param};
    while(arg_type.id()==ID_pointer)
    {
      std::list<exprt> args_deref_in=apply_dereference(args_in, SSA.ssa_value_ai[loc], SSA.ns);
      std::list<exprt> params_deref_in=apply_dereference(params_in, summary.value_domain_in, SSA.ns);

      local_SSAt::locationt next_loc=loc; ++next_loc;
      std::list<exprt> args_deref_out=apply_dereference(args_out, SSA.ssa_value_ai[next_loc], SSA.ns);
      std::list<exprt> params_deref_out=apply_dereference(params_out, summary.value_domain_out, SSA.ns);

      if(contains_advancer(params_deref_out))
      { 
        // If the caller contains advancers, bindings are different since objects from caller will
        // appear in the callee summary
        assert(!args_deref_in.empty() && !args_deref_out.empty());
        arg_type=SSA.ns.follow(args_deref_in.begin()->type());

        assert(arg_type.id()==ID_struct);

        for (const exprt &a : args_deref_in)
        {
          // Bind argument address
          address_of_exprt lhs_addr=address_of_exprt(a);
          rename(lhs_addr);

          address_of_exprt rhs_addr=address_of_exprt(a);
          typet symbol_type=args_out.begin()->type().subtype();
          symbol_type.set("#dynamic", params_deref_out.begin()->type().get_bool("#dynamic"));
          rhs_addr.object().type()=symbol_type;

          c.push_back(equal_exprt(lhs_addr, rhs_addr));

          for (auto &component : to_struct_type(arg_type).components())
          {
            // Bind argument members at the input
            symbol_exprt arg_member(
              id2string(to_symbol_expr(a).get_identifier())+"."+
              id2string(component.get_name()), component.type());

            symbol_exprt member_lhs_in=arg_member;
            rename(member_lhs_in);

            c.push_back(equal_exprt(member_lhs_in, SSA.read_rhs(arg_member, loc)));
          }
        }

        for (const exprt &a : args_deref_out)
        {
          for (auto &component : to_struct_type(arg_type).components())
          {
            // Bind argument members at the output (args_deref_out might contain different objects
            // than args_deref_in since function call may create new objects).
            symbol_exprt arg_member(id2string(to_symbol_expr(a).get_identifier()) + "." +
                                    id2string(component.get_name()), component.type());

            symbol_exprt member_lhs_out;
            if (find_corresponding_symbol(arg_member, summary.globals_out, member_lhs_out))
            {
              rename(member_lhs_out);
            }
            else
            {
              assert(find_corresponding_symbol(arg_member, cs_globals_in, member_lhs_out));
            }

            c.push_back(equal_exprt(member_lhs_out,
                                    SSA.name(ssa_objectt(arg_member, SSA.ns),
                                             local_SSAt::OUT,
                                             loc)));
          }
        }
      }
      else
      { // Bind objects pointed by argument and parameter when advancer is not present
        if (!args_deref_in.empty())
        {
          arg_type = SSA.ns.follow(args_deref_in.begin()->type());

          bind(transform_pointed_params_in(params_deref_in),
               transform_pointed_args_in(args_deref_in, SSA, loc),
               c);

          if (arg_type.id() == ID_struct)
          {
            for (auto &component : to_struct_type(arg_type).components())
            {
              bind(transform_pointed_member_params_in(params_deref_in, component),
                   transform_pointed_member_args_in(args_deref_in, component, SSA, loc),
                   c);
            }
          }
        }

        if (!args_deref_out.empty())
        {
          arg_type = SSA.ns.follow(args_deref_out.begin()->type());

          bind(transform_pointed_params_out(params_deref_out, summary.globals_out, arg_type),
               transform_pointed_args_out(args_deref_out, args_out.begin()->type().subtype(),
                                          params_deref_out.begin()->type(), SSA, loc),
               c);

          if (arg_type.id() == ID_struct)
          {
            for (auto &component : to_struct_type(arg_type).components())
            {
              bind(transform_pointed_member_params_out(params_deref_out, component,
                                                       summary.globals_out),
                   transform_pointed_member_args_out(args_deref_out, component, SSA, loc),
                   c);
            }
          }
        }
      }

      args_in = args_deref_in;
      args_out = args_deref_out;
      params_in = params_deref_in;
      params_out = params_deref_out;

      if (args_in.empty() && args_out.empty()) break;
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
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out,
  const summaryt &summary,
  const function_application_exprt &funapp_expr,
  const local_SSAt &SSA,
  const local_SSAt::locationt &loc)
{
  // equalities for globals_out
  exprt::operandst c;
  const irep_idt &ret_val_id=
      id2string(to_symbol_expr(funapp_expr.function()).get_identifier()) + "#return_value";
  for (summaryt::var_sett::const_iterator it=cs_globals_out.begin();
       it!=cs_globals_out.end(); it++)
  {
    symbol_exprt lhs;
    exprt rhs;


    if(get_original_identifier(*it)==ret_val_id)
    {
      // Bind function return value
      rhs=*it; // copy
      assert(find_corresponding_symbol(*it, summary.globals_out, lhs));
      rename(lhs);
      c.push_back(equal_exprt(lhs, rhs));

      typet type=SSA.ns.follow(rhs.type());

      std::list<exprt> callee_rv={*it};
      std::list<exprt> caller_rv={*it};

      // Bind all objects pointed by return value
      while(type.id()==ID_pointer)
      {
        local_SSAt::locationt next_loc=loc; ++next_loc;
        std::list<exprt> caller_rv_deref=
          apply_dereference(caller_rv, SSA.ssa_value_ai[next_loc], SSA.ns);
        std::list<exprt> callee_rv_deref=
          apply_dereference(callee_rv, summary.value_domain_out, SSA.ns);

        if(!callee_rv_deref.empty())
        {
          type=SSA.ns.follow(callee_rv_deref.begin()->type());
          bind(transform_pointed_params_out(
                 callee_rv_deref, summary.globals_out, type),
               transform_pointed_args_out(
                 caller_rv_deref,
                 caller_rv.begin()->type().subtype(),
                 callee_rv_deref.begin()->type(),
                 SSA,
                 loc),
               c);

          if(type.id()==ID_struct)
          {
            for(auto &component : to_struct_type(type).components())
            {
              bind(transform_pointed_member_params_out(
                     callee_rv_deref, component, summary.globals_out),
                   transform_pointed_member_args_out(
                     caller_rv_deref, component, SSA, loc),
                   c);
            }
          }
        }

        callee_rv=callee_rv_deref;
        caller_rv=caller_rv_deref;

        if(caller_rv.empty())
          break;
      }
    }
    else
    {
      if(id2string(it->get_identifier()).find("dynamic_object$")==std::string::npos &&
         id2string(it->get_identifier()).find("'obj")==std::string::npos)
      {
        rhs=*it; // copy
        if(find_corresponding_symbol(*it, summary.globals_out, lhs))
          rename(lhs);
        else
          assert(find_corresponding_symbol(*it, cs_globals_in, lhs));
        c.push_back(equal_exprt(lhs, rhs));
      }
    }
  }
  return conjunction(c);
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
  else if (expr.id() == ID_address_of)
  {
    irep_idt id;
    const exprt &obj = to_address_of_expr(expr).object();
    if (obj.id() == ID_symbol)
    {
      const std::string &obj_id = id2string(to_symbol_expr(obj).get_identifier());
      if (obj_id.compare(obj_id.length() - 4, 4, "'obj") == 0)
        id = obj_id.substr(0, obj_id.find_last_of("'"));
      else
        id = id2string(obj_id) + "'addr";

      id = id2string(id) + "@" + i2string(counter);
    }
    symbol_exprt addr_symbol(id, expr.type());
    expr = addr_symbol;
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
      // rename objects not present in globals in to non-suffix version
      symbol_exprt to_replace(get_original_identifier(*it), it->type());
      replace_map[*it]=to_replace;
      // to propagate #dynamic flag on type
      replace_map[to_replace]=to_replace;
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
         !(c=='l' || c=='b') &&
         !('0'<=c && c<='9'))
        pos=std::string::npos;
    }
  }
  if(pos!=std::string::npos)
    id=id.substr(0, pos);
  return id;
}

/*******************************************************************\

Function: ssa_inlinert::apply_dereference

  Inputs: Set of pointers and value analysis

 Outputs: Set of all objects that can be pointed by one of pointers
          from the input set.

 Purpose:

\*******************************************************************/

std::list<exprt> ssa_inlinert::apply_dereference(
  const std::list<exprt> &exprs,
  const ssa_value_domaint &value_domain,
  const namespacet &ns)
{
  std::list<exprt> result;
  for(const exprt &expr : exprs)
  {
    if(expr.id()==ID_symbol || expr.id()==ID_address_of)
    {
      exprt to_query=expr; // copy
      if(expr.id()==ID_symbol)
      {
        to_symbol_expr(to_query).set_identifier(get_original_identifier(to_symbol_expr(expr)));
      }
      ssa_value_domaint::valuest values=value_domain(to_query, ns);
      for(auto &v : values.value_set)
      {
        result.push_back(v.symbol_expr());
      }
    }
    else
    {
      assert(false);
    }
  }
  return result;
}

/*******************************************************************\

Function: ssa_inlinert::bind

  Inputs: Two sets of objects

 Outputs:

 Purpose: Create bindings between pairs of objects from given sets.

\*******************************************************************/

void ssa_inlinert::bind(
  const std::list<exprt> &lhs,
  const std::list<exprt> &rhs,
  exprt::operandst &bindings)
{
  exprt::operandst new_bind;
  for(const exprt &l : lhs)
  {
    for(const exprt &r : rhs)
    {
      new_bind.push_back(equal_exprt(l, r));
    }
  }
  if(!new_bind.empty())
    bindings.push_back(disjunction(new_bind));
}

std::list<exprt> ssa_inlinert::transform_pointed_params_in(const std::list<exprt> &params_in)
{
  std::list<exprt> result;
  for(const exprt &p : params_in)
  {
    symbol_exprt param_in=to_symbol_expr(p);
    rename(param_in);
    result.push_back(param_in);
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_args_in(
  const std::list<exprt> &args_in,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  std::list<exprt> result;
  for(const exprt &a : args_in)
  {
    result.push_back(SSA.read_rhs(a, loc));
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_member_params_in(
  const std::list<exprt> &params_in,
  const struct_union_typet::componentt &component)
{
  std::list<exprt> result;
  for(const exprt &p : params_in)
  {
    symbol_exprt param_member(
      id2string(to_symbol_expr(p).get_identifier())+"."+
      id2string(component.get_name()), component.type());
    rename(param_member);
    result.push_back(param_member);
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_member_args_in(
  const std::list<exprt> &args_in,
  const struct_union_typet::componentt &component,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  std::list<exprt> result;
  for(const exprt &a : args_in)
  {
    symbol_exprt arg_member(
      id2string(to_symbol_expr(a).get_identifier())+"."+
      id2string(component.get_name()), component.type());
    result.push_back(SSA.read_rhs(arg_member, loc));
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_params_out(
  const std::list<exprt> &params_out,
  const local_SSAt::var_sett &globals_out,
  const typet &param_type)
{
  std::list<exprt> result;
  for(const exprt &p : params_out)
  {
    symbol_exprt param_out;
    if (find_corresponding_symbol(to_symbol_expr(p), globals_out, param_out))
    {
      if (param_type.id()==ID_struct)
      {
        address_of_exprt param_addr=address_of_exprt(p);
        rename(param_addr);
        result.push_back(param_addr);
      }
      else
      {
        rename(param_out);
        result.push_back(param_out);
      }
    }
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_args_out(
  const std::list<exprt> &args_out,
  const typet &arg_symbol_type,
  const typet &param_type,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  std::list<exprt> result;

  const typet &arg_type=SSA.ns.follow(arg_symbol_type);
  for(const exprt &a : args_out)
  {
    if(arg_type.id()==ID_struct)
    {
      address_of_exprt arg_addr=address_of_exprt(a);
      typet symbol_type=arg_symbol_type;
      symbol_type.set("#dynamic", param_type.get_bool("#dynamic"));
      arg_addr.object().type()=symbol_type;
      result.push_back(arg_addr);
    }
    else
    {
      result.push_back(SSA.name(ssa_objectt(a, SSA.ns), local_SSAt::OUT, loc));
    }
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_member_params_out(
  const std::list<exprt> &params_out,
  const struct_union_typet::componentt &component,
  const local_SSAt::var_sett &globals_out)
{
  std::list<exprt> result;
  for(const exprt &p : params_out)
  {
    symbol_exprt param_member(
      id2string(to_symbol_expr(p).get_identifier())+"."+
      id2string(component.get_name()), component.type());
    symbol_exprt param_out;
    if(find_corresponding_symbol(param_member, globals_out, param_out))
    {
      rename(param_out);
      result.push_back(param_out);
    }
  }
  return result;
}

std::list<exprt> ssa_inlinert::transform_pointed_member_args_out(
  const std::list<exprt> &args_out,
  const struct_union_typet::componentt &component,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  std::list<exprt> result;
  for(const exprt &a : args_out)
  {
    symbol_exprt arg_member(
      id2string(to_symbol_expr(a).get_identifier()) + "." +
      id2string(component.get_name()), component.type());
    result.push_back(SSA.name(ssa_objectt(arg_member, SSA.ns), local_SSAt::OUT, loc));
  }
  return result;
}

/*******************************************************************\

Function: ssa_inlinert::contains_advancer

  Inputs: List of expressions

 Outputs: True if the list contains an advancer

 Purpose:

\*******************************************************************/

bool ssa_inlinert::contains_advancer(const std::list<exprt> &params)
{
  for(const exprt &p : params)
  {
    if(p.id()==ID_symbol &&
       id2string(to_symbol_expr(p).get_identifier()).find("'adv") != std::string::npos)
    {
      return true;
    }
  }
  return false;
}

