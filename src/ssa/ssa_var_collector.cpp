/*******************************************************************\

Module: Template Generator for Summaries, Invariants and Preconditions

Author: Peter Schrammel, Stefan Marticek

\*******************************************************************/

/// \file
/// Template Generator for Summaries, Invariants and Preconditions

#include "ssa_var_collector.h"

void ssa_var_collectort::add_var(
  const domaint::vart &var,
  const domaint::guardt &pre_guard,
  domaint::guardt post_guard,
  const domaint::kindt &kind,
  domaint::var_specst &var_specs)
{
  exprt aux_expr=true_exprt();
  if(std_invariants && pre_guard.id()==ID_and)
  {
    exprt init_guard=and_exprt(pre_guard.op0(), not_exprt(pre_guard.op1()));
    exprt post_var=post_renaming_map[var];
    exprt aux_var=aux_renaming_map[var];
    exprt aux_equals_post=equal_exprt(aux_var, post_var);
    exprt aux_equals_init=equal_exprt(aux_var, init_renaming_map[var]);
    aux_expr=
      and_exprt(
        implies_exprt(
          and_exprt(post_guard, not_exprt(init_guard)),
          aux_equals_post),
        implies_exprt(
          init_guard,
          aux_equals_init));
    post_guard=or_exprt(post_guard, init_guard);
  }
  if(var.type().id()!=ID_array)
  {
    var_specs.push_back(domaint::var_spect());
    domaint::var_spect &var_spec=var_specs.back();
    var_spec.pre_guard=pre_guard;
    var_spec.post_guard=post_guard;
    var_spec.aux_expr=aux_expr;
    var_spec.kind=kind;
    var_spec.var=var;
  }

  // arrays
  if(var.type().id()==ID_array && options.get_bool_option("arrays"))
  {
    const array_typet &array_type=to_array_type(var.type());
    mp_integer size;
    to_integer(array_type.size(), size);
    for(mp_integer i=0; i<size; i=i+1)
    {
      var_specs.push_back(domaint::var_spect());
      domaint::var_spect &var_spec=var_specs.back();
      constant_exprt index=from_integer(i, array_type.size().type());
      var_spec.pre_guard=pre_guard;
      var_spec.post_guard=post_guard;
      var_spec.aux_expr=aux_expr;
      var_spec.kind=kind;
      var_spec.var=index_exprt(var, index);
    }
  }
}

void ssa_var_collectort::get_pre_post_guards(
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  exprt &pre_guard,
  exprt &post_guard)
{
#if 0
  std::cout << "post-location: "
            << n_it->location->location_number << std::endl;
  assert(n_it->loophead!=SSA.nodes.end());
  std::cout << "pre-location: "
            << n_it->loophead->location->location_number << std::endl;
#endif
  exprt lhguard=SSA.guard_symbol(n_it->loophead->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(lhguard), *n_it, true);
  exprt lsguard=
    SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard), *n_it, true);
  pre_guard=and_exprt(lhguard, lsguard);

  exprt pguard=SSA.guard_symbol(n_it->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(pguard), *n_it, false);
  exprt pcond=SSA.cond_symbol(n_it->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(pcond), *n_it, false);
  post_guard=and_exprt(pguard, pcond);
}

void ssa_var_collectort::get_pre_var(
  const local_SSAt &SSA,
  local_SSAt::objectst::const_iterator o_it,
  local_SSAt::nodest::const_iterator n_it,
  symbol_exprt &pre_var)
{
  pre_var=SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
  ssa_local_unwinder.unwinder_rename(pre_var, *n_it, true);

  symbol_exprt post_var=SSA.read_rhs(*o_it, n_it->location);
  ssa_local_unwinder.unwinder_rename(post_var, *n_it, false);
  post_renaming_map[pre_var]=post_var;

  rename_aux_post(post_var);
  aux_renaming_map[pre_var]=post_var;
}

/// supposes that loop head PHIs are of the form xphi=gls?xlb:x0
void ssa_var_collectort::get_init_expr(
  const local_SSAt &SSA,
  local_SSAt::objectst::const_iterator o_it,
  local_SSAt::nodest::const_iterator n_it,
  exprt &init_expr)
{
  symbol_exprt phi_var=
    SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
  ssa_local_unwinder.unwinder_rename(phi_var, *n_it->loophead, true);
  for(local_SSAt::nodet::equalitiest::const_iterator e_it=
        n_it->loophead->equalities.begin();
      e_it!=n_it->loophead->equalities.end(); e_it++)
  {
    if(e_it->rhs().id()==ID_if &&
       to_symbol_expr(e_it->lhs()).get_identifier()==phi_var.get_identifier())
    {
      const if_exprt &if_expr=to_if_expr(e_it->rhs());
      init_expr=if_expr.false_case();
      // should already be renamed for inner loops
      break;
    }
  }

  symbol_exprt pre_var=SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
  ssa_local_unwinder.unwinder_rename(pre_var, *n_it, true);
  init_renaming_map[pre_var]=init_expr;
}

void ssa_var_collectort::collect_variables_loop(
  const local_SSAt &SSA,
  bool forward)
{
  // used for renaming map
  var_listt pre_state_vars, post_state_vars;

  // add loop variables
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead!=SSA.nodes.end()) // we've found a loop
    {
      exprt pre_guard, post_guard;
      get_pre_post_guards(SSA, n_it, pre_guard, post_guard);

      const ssa_domaint::phi_nodest &phi_nodes=
        SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

      // Record the objects modified by the loop to get
      // 'primed' (post-state) and 'unprimed' (pre-state) variables.
      for(local_SSAt::objectst::const_iterator
            o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::phi_nodest::const_iterator p_it=
          phi_nodes.find(o_it->get_identifier());

        if(p_it==phi_nodes.end())
          continue; // object not modified in this loop

        symbol_exprt pre_var;
        get_pre_var(SSA, o_it, n_it, pre_var);
        exprt init_expr;
        get_init_expr(SSA, o_it, n_it, init_expr);
        add_var(pre_var, pre_guard, post_guard, domaint::LOOP, var_specs);

#ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " "
                  << from_expr(ns, "", out) << std::endl;
#endif
      }
    }
  }
}
