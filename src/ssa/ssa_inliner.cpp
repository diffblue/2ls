/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// SSA Inliner

#include <algorithm>

#include <util/i2string.h>
#include <util/replace_expr.h>

#include "ssa_inliner.h"

/// get summary for function call
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

  covered_cs_heap_out.clear();

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

  bindings.push_back(get_replace_new_objects(SSA, *f_it, loc, summary));

  // equalities for arguments
  bindings.push_back(
    get_replace_params(
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
  summaries.push_back(
    implies_exprt(SSA.guard_symbol(n_it->location), transformer));

  // equalities for globals out (including unmodified globals)
  if(forward)
    bindings.push_back(
      get_replace_globals_out(
        cs_globals_in,
        cs_globals_out,
        summary,
        *f_it,
        SSA,
        loc));
  else
    bindings.push_back(
      get_replace_globals_out(
        cs_globals_out,
        cs_globals_in,
        summary,
        *f_it,
        SSA,
        loc));
}

/// get summary for all function calls
exprt ssa_inlinert::get_summaries(const local_SSAt &SSA)
{
  exprt::operandst summaries, bindings;
  get_summaries(SSA, true, summaries, bindings);
  return and_exprt(conjunction(bindings), conjunction(summaries));
}

/// get summary for all function calls up to a given location
exprt ssa_inlinert::get_summaries_to_loc(
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  exprt::operandst summaries, bindings;
  get_summaries(SSA, true, summaries, bindings, loc);
  return and_exprt(conjunction(bindings), conjunction(summaries));
}

/// get summary for all function calls
void ssa_inlinert::get_summaries(
  const local_SSAt &SSA,
  bool forward,
  exprt::operandst &summaries,
  exprt::operandst &bindings,
  local_SSAt::locationt loc)
{
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(loc!=local_SSAt::locationt() &&
       n_it->location->location_number>=loc->location_number)
      return;
    for(local_SSAt::nodet::function_callst::const_iterator f_it=
          n_it->function_calls.begin();
        f_it!=n_it->function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); // no function pointers
      irep_idt fname=to_symbol_expr(f_it->function()).get_identifier();

      if(summary_db.exists(fname))
      {
        get_summary(
          SSA, n_it, f_it, summary_db.get(fname), forward, summaries, bindings);
      }
    }
  }
}

/// replaces function calls by summaries if available in the summary store and
/// does nothing otherwise
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

/// replaces inlines functions if SSA is available in functions and does nothing
/// otherwise
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

/// inline summary
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
      implies_exprt(
        SSA.guard_symbol(node->location),
        precondition));
  }
  else
  {
    rename(precondition);
    node->assertions.push_back(
      implies_exprt(
        SSA.guard_symbol(node->location),
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

/// inline function
///
/// Remark: local_SSAt::nodest maps a goto program target to a single SSA node,
///         when inlining several calls to the same function
///         instructions appear factorized by the goto program targets
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
    if(!is_pointed(*it))
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
    if(funapp_expr.arguments().size()!=params.size() &&
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
      std::list<exprt> args_deref_in=
        apply_dereference(args_in, SSA.ssa_value_ai[loc], SSA.ns);
      std::list<exprt> params_deref_in=
        apply_dereference(params_in, summary.value_domain_in, SSA.ns);

      local_SSAt::locationt next_loc=loc;
      ++next_loc;
      std::list<exprt> args_deref_out=
        apply_dereference(args_out, SSA.ssa_value_ai[next_loc], SSA.ns);
      std::list<exprt> params_deref_out=
        apply_dereference(params_out, summary.value_domain_out, SSA.ns);

      const typet arg_symbol_type=arg_type.subtype();
      arg_type=SSA.ns.follow(arg_symbol_type);

      if(contains_iterator(params_deref_out))
      { // If the caller contains iterators, bindings are different since
        // objects from caller will appear in the callee summary
        assert(!args_deref_in.empty() && !args_deref_out.empty());

        arg_type=SSA.ns.follow(args_deref_in.begin()->type());
        assert(arg_type.id()==ID_struct);

        for(const exprt &a : args_deref_in)
        {
          std::list<exprt> aliases=
            apply_dereference({a}, SSA.ssa_value_ai[next_loc], SSA.ns);
          aliases.push_front(a);

          for(auto &alias : aliases)
          {
            const exprt lhs_expr=
              param_out_transformer(alias, arg_type, summary.globals_out);
            const exprt rhs_expr=
              arg_out_transformer(
                alias,
                arg_symbol_type,
                params_deref_out.begin()->type(),
                SSA,
                loc);
            // Bind argument address
            c.push_back(equal_exprt(lhs_expr, rhs_expr));

            for(auto &component : to_struct_type(arg_type).components())
            {
              const exprt lhs_comp_expr=
                param_in_member_transformer(alias, component);
              const exprt rhs_comp_expr=
                arg_in_member_transformer(alias, component, SSA, loc);
              // Bind argument members at the input
              c.push_back(equal_exprt(lhs_comp_expr, rhs_comp_expr));
            }
          }
        }

        for(const exprt &a : args_deref_out)
        {
          std::list<exprt> aliases=
            apply_dereference({a}, SSA.ssa_value_ai[next_loc], SSA.ns);
          aliases.push_front(a);
          for(auto &alias : aliases)
          {
            const typet &alias_type=SSA.ns.follow(alias.type());
            assert(alias_type.id()==ID_struct);
            for(auto &component : to_struct_type(alias_type).components())
            {
              // Bind argument members at the output (args_deref_out might
              // contain different objects than args_deref_in since function
              // call may create new objects).
              symbol_exprt arg_member(
                id2string(to_symbol_expr(alias).get_identifier())+"."+
                id2string(component.get_name()), component.type());

              symbol_exprt member_lhs_out;
              if(find_corresponding_symbol(
                 arg_member, summary.globals_out, member_lhs_out))
              {
                rename(member_lhs_out);
                const exprt arg_out=
                  arg_out_member_transformer(alias, component, SSA, loc);
                c.push_back(equal_exprt(member_lhs_out, arg_out));
              }
            }
          }
        }
      }
      else
      {
        // Bind objects pointed by argument and parameter when iterator is
        // not present
        if(params_deref_in.size()==1)
        {
          const exprt &p_in=params_deref_in.front();

          exprt::operandst d;
          for(const exprt &a_in : args_deref_in)
          {
            exprt::operandst binding;
            const exprt lhs_expr=param_in_transformer(p_in);
            const exprt rhs_expr=arg_in_transformer(a_in, SSA, loc);
            binding.push_back(equal_exprt(lhs_expr, rhs_expr));

            if(arg_type.id()==ID_struct)
            {
              for(auto &component : to_struct_type(arg_type).components())
              {
                const exprt lhs_comp_expr=
                  param_in_member_transformer(p_in, component);
                const exprt rhs_comp_expr=
                  arg_in_member_transformer(a_in, component, SSA, loc);
                binding.push_back(equal_exprt(lhs_comp_expr, rhs_comp_expr));
              }
            }
            d.push_back(conjunction(binding));
          }
          if(!d.empty())
            c.push_back(disjunction(d));

          d.clear();
          for(const exprt &p_out : params_deref_out)
          {
            for(const exprt &a_out : args_deref_out)
            {
              if(!cs_heap_covered(a_out))
              {
                exprt::operandst binding;

                const exprt lhs_expr=
                  param_out_transformer(p_out, arg_type, summary.globals_out);
                const exprt rhs_expr=
                  arg_out_transformer(
                    a_out,
                    arg_symbol_type,
                    p_out.type(),
                    SSA,
                    loc);
                binding.push_back(equal_exprt(lhs_expr, rhs_expr));

                if(arg_type.id()==ID_struct)
                {
                  for(auto &component : to_struct_type(arg_type).components())
                  {
                    const exprt lhs_comp_expr=
                      param_out_member_transformer(
                        p_out,
                        component,
                        summary.globals_out);
                    const exprt rhs_comp_expr=
                      arg_out_member_transformer(a_out, component, SSA, loc);
                    binding.push_back(
                      equal_exprt(
                        lhs_comp_expr,
                        rhs_comp_expr));
                  }
                }
                d.push_back(conjunction(binding));
              }
            }
          }
          if(!d.empty())
            c.push_back(disjunction(d));
        }
      }

      args_in=args_deref_in;
      args_out=args_deref_out;
      params_in=params_deref_in;
      params_out=params_deref_out;

      if(args_in.empty() && args_out.empty())
        break;
    }
  }
  return conjunction(c);
}

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

/// equalities for globals out (including unmodified globals)
exprt ssa_inlinert::get_replace_globals_out(
  const local_SSAt::var_sett &cs_globals_in,
  const local_SSAt::var_sett &cs_globals_out,
  const summaryt &summary,
  const function_application_exprt &funapp_expr,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  // equalities for globals_out
  exprt::operandst c;
  for(summaryt::var_sett::const_iterator it=cs_globals_out.begin();
      it!=cs_globals_out.end(); it++)
  {
    symbol_exprt lhs;
    const exprt rhs=*it;


    if(is_pointed(*it) ||
       id2string(it->get_identifier()).find("dynamic_object$")!=
       std::string::npos)
    {
      if(!cs_heap_covered(*it) &&
         !find_corresponding_symbol(*it, summary.globals_out, lhs))
      {
        assert(find_corresponding_symbol(*it, cs_globals_in, lhs));
        c.push_back(equal_exprt(lhs, rhs));
      }
    }
    else
    {
      if(find_corresponding_symbol(*it, summary.globals_out, lhs))
      {
        // Bind function return value
        rename(lhs);
        c.push_back(equal_exprt(lhs, rhs));

        typet type=SSA.ns.follow(rhs.type());

        std::list<exprt> callee_global={*it};
        std::list<exprt> caller_global={*it};

        // Bind all objects pointed by return value
        while(type.id()==ID_pointer)
        {
          local_SSAt::locationt next_loc=loc;
          ++next_loc;
          std::list<exprt> caller_deref=
            apply_dereference(
              caller_global,
              SSA.ssa_value_ai[next_loc],
              SSA.ns);
          std::list<exprt> callee_deref=
            apply_dereference(callee_global, summary.value_domain_out, SSA.ns);

          if(!callee_deref.empty())
          {
            const typet symbol_type=type.subtype();
            type=SSA.ns.follow(symbol_type);

            exprt::operandst d;
            for(const exprt &callee : callee_deref)
            {
              for(const exprt &caller : caller_deref)
              {
                if(!cs_heap_covered(caller))
                {
                  exprt::operandst binding;
                  const exprt lhs_expr=
                    param_out_transformer(callee, type, summary.globals_out);
                  const exprt rhs_expr=
                    arg_out_transformer(
                      caller,
                      symbol_type,
                      callee.type(),
                      SSA,
                      loc);
                  binding.push_back(equal_exprt(lhs_expr, rhs_expr));

                  if(type.id()==ID_struct)
                  {
                    for(auto &component : to_struct_type(type).components())
                    {
                      const exprt lhs_comp_expr=
                        param_out_member_transformer(
                          callee,
                          component,
                          summary.globals_out);
                      const exprt rhs_comp_expr=
                        arg_out_member_transformer(caller, component, SSA, loc);
                      binding.push_back(
                        equal_exprt(
                          lhs_comp_expr,
                          rhs_comp_expr));
                    }
                  }

                  d.push_back(conjunction(binding));
                }
              }
            }

            if(!d.empty())
              c.push_back(disjunction(d));
          }

          callee_global=callee_deref;
          caller_global=caller_deref;

          if(caller_global.empty())
            break;
        }
      }
      else
      {
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

/// equalities for globals out (including unmodified globals)
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

void ssa_inlinert::havoc(
  local_SSAt::nodet &node,
  local_SSAt::nodet::function_callst::iterator f_it)
{
  // remove function call
  rm_function_calls.insert(f_it);
}

void ssa_inlinert::rename(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &sexpr=to_symbol_expr(expr);
    irep_idt id=id2string(sexpr.get_identifier())+"@"+i2string(counter);
    sexpr.set_identifier(id);
  }
  else if(expr.id()==ID_address_of)
  {
    irep_idt id;
    const exprt &obj=to_address_of_expr(expr).object();
    if(obj.id()==ID_symbol)
    {
      const std::string &obj_id=id2string(to_symbol_expr(obj).get_identifier());
      if(is_pointed(obj))
        id=get_pointer_id(obj);
      else
        id=id2string(obj_id)+"'addr";

      id=id2string(id)+"@"+i2string(counter);
    }
    symbol_exprt addr_symbol(id, expr.type());
    expr=addr_symbol;
  }
  Forall_operands(op, expr)
    rename(*op);
}

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

  replace_expr(replace_map, expr);

  // arguments might contain globals, thus, we have to replace them separately
  replace_map.clear();

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

/// apply changes to node, must be called after replace and havoc (needed
/// because replace and havoc usually called while iterating over equalities,
/// and hence we cannot modify them)
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

/// returns true if no nodes were to be committed
bool ssa_inlinert::commit_nodes(
  local_SSAt::nodest &nodes,
  local_SSAt::nodest::iterator n_pos)
{
  if(new_nodes.empty())
    return true;
  nodes.splice(n_pos, new_nodes, new_nodes.begin(), new_nodes.end());
  return false;
}

/// \return returns false if the symbol is not found
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

/// TODO: this is a potential source of bugs. Better way to do that?
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
      if(c=='#' || c=='@' || c=='%' || c=='!')
        pos=i;
    }
    else
    {
      if(!(c=='#' || c=='@' || c=='%' || c=='!') &&
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

/// \par parameters: Set of pointers and value analysis
/// \return Set of all objects that can be pointed by one of pointers from the
///   input set.
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
        to_symbol_expr(to_query).set_identifier(
          get_original_identifier(to_symbol_expr(expr)));
      }
      ssa_value_domaint::valuest values=value_domain(to_query, ns);
      for(const ssa_objectt &v : values.value_set)
      {
        assert(v.get_expr().id()==ID_symbol);
        result.push_back(v.get_expr());
      }
    }
    else if(expr.id()==ID_typecast)
    {
      std::list<exprt> tmp=apply_dereference(
        {to_typecast_expr(expr).op()}, value_domain, ns);
      for(auto &e : tmp)
        result.push_back(e);
    }
  }
  return result;
}

/// \par parameters: List of expressions
/// \return True if the list contains an advancer
bool ssa_inlinert::contains_iterator(const std::list<exprt> &params)
{
  auto it=std::find_if(
    params.begin(),
    params.end(),
    [](const exprt &p) { return is_iterator(p); });
  return (it!=params.end());
}

exprt ssa_inlinert::param_in_transformer(const exprt &param)
{
  assert(param.id()==ID_symbol);
  symbol_exprt param_in=to_symbol_expr(param);
  rename(param_in);
  return param_in;
}

exprt ssa_inlinert::arg_in_transformer(
  const exprt &arg,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  return SSA.read_rhs(arg, loc);
}

exprt ssa_inlinert::param_in_member_transformer(
  const exprt &param,
  const struct_union_typet::componentt &component)
{
  assert(param.id()==ID_symbol);
  symbol_exprt param_member(
    id2string(to_symbol_expr(param).get_identifier())+"."+
    id2string(component.get_name()), component.type());
  rename(param_member);
  return param_member;
}

exprt ssa_inlinert::arg_in_member_transformer(
  const exprt &arg,
  const struct_union_typet::componentt &component,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  symbol_exprt arg_member(
    id2string(to_symbol_expr(arg).get_identifier())+"."+
      id2string(component.get_name()),
    component.type());
  return SSA.read_rhs(arg_member, loc);
}

exprt ssa_inlinert::param_out_transformer(
  const exprt &param,
  const typet &type,
  const local_SSAt::var_sett &globals_out)
{
  assert(param.id()==ID_symbol);

  if(type.id()==ID_struct)
  {
    address_of_exprt param_addr=address_of_exprt(param);
    rename(param_addr);
    return param_addr;
  }
  else
  {
    symbol_exprt param_out=to_symbol_expr(param);
    if(find_corresponding_symbol(to_symbol_expr(param), globals_out, param_out))
      rename(param_out);
    return param_out;
  }
}

exprt ssa_inlinert::arg_out_transformer(
  const exprt &arg,
  const typet &arg_symbol_type,
  const typet &param_type,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  const typet &arg_type=SSA.ns.follow(arg_symbol_type);
  if(arg_type.id()==ID_struct)
  {
    assert(arg.id()==ID_symbol);
    symbol_exprt arg_symbol=to_symbol_expr(arg);
    address_of_exprt arg_addr=address_of_exprt(arg_symbol);

    const symbolt *symbol;
    if(!SSA.ns.lookup(arg_symbol.get_identifier(), symbol))
    {
      arg_addr=address_of_exprt(symbol->symbol_expr());
    }

    covered_cs_heap_out.insert(arg_symbol);
    return arg_addr;
  }
  else
  {
    const symbol_exprt &arg_out=
      SSA.name(ssa_objectt(arg, SSA.ns), local_SSAt::OUT, loc);
    covered_cs_heap_out.insert(arg_out);
    return arg_out;
  }
}

exprt ssa_inlinert::param_out_member_transformer(
  const exprt &param,
  const struct_union_typet::componentt &component,
  const local_SSAt::var_sett &globals_out)
{
  assert(param.id()==ID_symbol);

  symbol_exprt param_member(
    id2string(to_symbol_expr(param).get_identifier())+"."+
    id2string(component.get_name()), component.type());
  symbol_exprt param_out;
  assert(find_corresponding_symbol(param_member, globals_out, param_out));
  rename(param_out);
  return param_out;
}

exprt ssa_inlinert::arg_out_member_transformer(
  const exprt &arg,
  const struct_union_typet::componentt &component,
  const local_SSAt &SSA,
  local_SSAt::locationt loc)
{
  symbol_exprt arg_member(
    id2string(to_symbol_expr(arg).get_identifier())+"."+
    id2string(component.get_name()), component.type());
  const symbol_exprt &arg_member_out=
    SSA.name(ssa_objectt(arg_member, SSA.ns), local_SSAt::OUT, loc);
  covered_cs_heap_out.insert(arg_member_out);
  return arg_member_out;
}

bool ssa_inlinert::cs_heap_covered(const exprt &expr)
{
  return expr.id()==ID_symbol &&
         covered_cs_heap_out.find(to_symbol_expr(expr))!=
         covered_cs_heap_out.end();
}

exprt ssa_inlinert::get_replace_new_objects(
  const local_SSAt &SSA,
  const function_application_exprt funapp_expr,
  local_SSAt::locationt loc,
  const summaryt &summary)
{
  exprt::operandst binding;

  const irep_idt &fname=to_symbol_expr(funapp_expr.function()).get_identifier();

  auto next_loc=loc;
  ++next_loc;
  if(SSA.heap_analysis.has_location(next_loc))
  {
    const ssa_heap_domaint &heap_domain=SSA.heap_analysis[next_loc];

    const std::list<symbol_exprt> callee_objects=
      heap_domain.new_objects(fname);
    const std::list<symbol_exprt> caller_objects=
      heap_domain.new_caller_objects(fname, loc);

    auto callee_it=callee_objects.begin();
    for(auto caller_it=caller_objects.begin(); caller_it!=caller_objects.end();
        ++caller_it, ++callee_it)
    {
      const typet symbol_type=caller_it->type();
      const typet type=SSA.ns.follow(symbol_type);

      const exprt lhs_expr=
        param_out_transformer(*callee_it, type, summary.globals_out);
      const exprt rhs_expr=
        arg_out_transformer(*caller_it, symbol_type, type, SSA, loc);
      binding.push_back(equal_exprt(lhs_expr, rhs_expr));

      if(type.id()==ID_struct)
      {
        for(auto &component : to_struct_type(type).components())
        {
          const exprt lhs_comp_expr=
            param_out_member_transformer(
              *callee_it,
              component,
              summary.globals_out);
          const exprt rhs_comp_expr=
            arg_out_member_transformer(*caller_it, component, SSA, loc);
          binding.push_back(equal_exprt(lhs_comp_expr, rhs_comp_expr));
        }
      }
    }
  }

  return conjunction(binding);
}
