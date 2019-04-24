/*******************************************************************\

Module: Template Generator Base

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator Base

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/mp_arith.h>

#include <ssa/ssa_inliner.h>

#include "template_generator_base.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"
#include "predabs_domain.h"
#include "heap_domain.h"
#include "heap_tpolyhedra_domain.h"
#include "heap_tpolyhedra_sympath_domain.h"

#ifdef DEBUG
#include <iostream>
#endif

void template_generator_baset::get_pre_post_guards(
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

void template_generator_baset::get_pre_var(
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
void template_generator_baset::get_init_expr(
  const local_SSAt &SSA,
  local_SSAt::objectst::const_iterator o_it,
  local_SSAt::nodest::const_iterator n_it,
  exprt &init_expr)
{
  symbol_exprt phi_var=
    SSA.name(*o_it, local_SSAt::PHI, n_it->loophead->location);
  ssa_local_unwinder.unwinder_rename(phi_var, *n_it->loophead, true);
  for(const auto &e : n_it->loophead->equalities)
  {
    if(e.rhs().id()==ID_if &&
       to_symbol_expr(e.lhs()).get_identifier()==phi_var.get_identifier())
    {
      const if_exprt &if_expr=to_if_expr(e.rhs());
      init_expr=if_expr.false_case();
      // should already be renamed for inner loops
      break;
    }
  }

  symbol_exprt pre_var=SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
  ssa_local_unwinder.unwinder_rename(pre_var, *n_it, true);
  init_renaming_map[pre_var]=init_expr;
}

void template_generator_baset::collect_variables_loop(
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
        const std::string id=id2string(o_it->get_identifier());
        ssa_domaint::phi_nodest::const_iterator p_it=phi_nodes.find(id);

        if(p_it==phi_nodes.end()) // object not modified in this loop
          continue;

        exprt obj_post_guard=post_guard;

        if(id.find("__CPROVER_deallocated")!=std::string::npos)
        {
          auto record_frees=collect_record_frees(SSA, n_it->loophead, n_it);
          exprt::operandst d;
          for(auto &r : record_frees)
            d.push_back(equal_exprt(r, true_exprt()));
          if(!d.empty())
            obj_post_guard=and_exprt(obj_post_guard, disjunction(d));
        }

        symbol_exprt pre_var;
        get_pre_var(SSA, o_it, n_it, pre_var);

        // For fields of dynamic objects, we add a guard that their value is not
        // equal to the corresponding input SSA variable that represents a state
        // when the object is not allocated.
        // Example: dynamic_object$0.next#ls100 != dynamic_object$0.next
        if(id.find("ssa::dynamic_object$")!=std::string::npos)
        {
          exprt &post_var=post_renaming_map[pre_var];
          assert(post_var.id()==ID_symbol);
          const irep_idt orig_id=get_original_name(to_symbol_expr(post_var));
          symbol_exprt unallocated(orig_id, post_var.type());
          exprt guard=not_exprt(equal_exprt(post_var, unallocated));
          obj_post_guard=and_exprt(obj_post_guard, guard);
        }

        exprt init_expr;
        get_init_expr(SSA, o_it, n_it, init_expr);
        add_var(pre_var, pre_guard, obj_post_guard, domaint::LOOP, var_specs);

#ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " " <<
          from_expr(ns, "", out) << std::endl;
#endif
      }
    }
  }
}

domaint::var_sett template_generator_baset::all_vars()
{
  domaint::var_sett vars;
  for(const auto &v : var_specs)
  {
    vars.insert(v.var);
  }
  return vars;
}

void template_generator_baset::filter_template_domain()
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(const auto &v : new_var_specs)
  {
    const domaint::vart &s=v.var;

#ifdef DEBUG
    std::cout << "var: " << s << std::endl;
#endif

    if((s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
        s.type().id()==ID_floatbv /*|| s.type().id()==ID_c_enum_tag*/))
    {
      var_specs.push_back(v);
    }
  }
}

void template_generator_baset::filter_equality_domain()
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(const auto &v : new_var_specs)
  {
    var_specs.push_back(v);
  }
}

void template_generator_baset::filter_heap_domain()
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(auto &var : new_var_specs)
  {
    if(var.var.id()==ID_symbol && var.var.type().id()==ID_pointer)
    {
      if(is_pointed(var.var) &&
         id2string(to_symbol_expr(var.var).get_identifier()).find(".")!=
         std::string::npos)
        continue;
      // Filter out non-assigned OUT variables
      if(var.kind!=domaint::OUT ||
         ssa_inlinert::get_original_identifier(to_symbol_expr(var.var))!=
         to_symbol_expr(var.var).get_identifier())
        var_specs.push_back(var);
    }
  }
}

void template_generator_baset::add_var(
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
    aux_expr=and_exprt(
      implies_exprt(
        and_exprt(post_guard, not_exprt(init_guard)),
        equal_exprt(aux_var, post_var)),
      implies_exprt(init_guard, equal_exprt(aux_var, init_renaming_map[var])));
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

void template_generator_baset::add_vars(
  const local_SSAt::var_listt &vars_to_add,
  const domaint::guardt &pre_guard,
  const domaint::guardt &post_guard,
  const domaint::kindt &kind,
  domaint::var_specst &var_specs)
{
  for(const auto &v : vars_to_add)
    add_var(v, pre_guard, post_guard, kind, var_specs);
}

void template_generator_baset::add_vars(
  const local_SSAt::var_sett &vars_to_add,
  const domaint::guardt &pre_guard,
  const domaint::guardt &post_guard,
  const domaint::kindt &kind,
  domaint::var_specst &var_specs)
{
  for(const auto &v : vars_to_add)
    add_var(v, pre_guard, post_guard, kind, var_specs);
}

void template_generator_baset::add_vars(
  const var_listt &vars_to_add,
  const domaint::guardt &pre_guard,
  const domaint::guardt &post_guard,
  const domaint::kindt &kind,
  domaint::var_specst &var_specs)
{
  for(const auto &v : vars_to_add)
    add_var(v, pre_guard, post_guard, kind, var_specs);
}

void template_generator_baset::handle_special_functions(const local_SSAt &SSA)
{
  const irep_idt &function_id=
    SSA.goto_function.body.instructions.front().function;
  if(id2string(function_id)=="__CPROVER_initialize")
  {
    options.set_option("intervals", true);
    options.set_option("enum-solver", true);
  }
}

/// rename custom template to correct SSA identifiers
bool template_generator_baset::replace_post(
  replace_mapt replace_map,
  exprt &expr)
{
  bool replaced=false;
  if(expr.id()==ID_function_application)
  {
    const function_application_exprt &f=to_function_application_expr(expr);
    if(f.function().get(ID_identifier)==TEMPLATE_NEWVAR)
    {
      assert(f.arguments().size()==1);
      if(f.arguments()[0].id()==ID_typecast)
        expr=replace_map[f.arguments()[0].op0()];
      else
        expr=replace_map[f.arguments()[0]];
      return true;
    }
  }
  for(unsigned i=0; i<expr.operands().size(); i++)
  {
    bool _replaced=replace_post(replace_map, expr.operands()[i]);
    replaced=replaced || _replaced;
  }
  return replaced;
}

bool template_generator_baset::build_custom_expr(
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator n_it,
  exprt &expr)
{
  replace_mapt replace_map, replace_post_map;

  const ssa_domaint::phi_nodest &phi_nodes=
    SSA.ssa_analysis[n_it->loophead->location].phi_nodes;

  for(const auto &object : SSA.ssa_objects.objects)
  {
    ssa_domaint::phi_nodest::const_iterator p_it=
      phi_nodes.find(object.get_identifier());

    if(p_it!=phi_nodes.end()) // modified in loop
    {
      // rename to pre
      replace_map[object.get_expr()]=
        SSA.name(object, local_SSAt::LOOP_BACK, n_it->location);

      // rename to post
      replace_post_map[object.get_expr()]=
        SSA.read_rhs(object, n_it->location);
      // TODO: unwinding
    }
    else // not modified in loop
    {
      // rename to id valid at loop head
      replace_map[object.get_expr()]=
        SSA.read_rhs(object, n_it->loophead->location);
      // TODO: unwinding
    }
  }

  bool contains_newvar=replace_post(replace_post_map, expr);
  replace_expr(replace_map, expr);
  return contains_newvar;
}

/// [experimental]
bool template_generator_baset::instantiate_custom_templates(
  const local_SSAt &SSA)
{
  // TODO: the code below cannot work for unwound SSA
  //  we deactivate it for now
  return false;

  // used for renaming map
  var_listt pre_state_vars, post_state_vars;

  bool found_poly=false, found_predabs=false;
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead!=SSA.nodes.end()) // we've found a loop
    {
      exprt pre_guard, post_guard, aux_expr;
      get_pre_post_guards(SSA, n_it, pre_guard, post_guard);
      aux_expr=true_exprt(); // TODO: change to "standard" invariant semantics
      bool add_post_vars=false;

      // search for templates in the loop
      for(local_SSAt::nodest::const_iterator nn_it=n_it->loophead;
          nn_it!=n_it; nn_it++)
      {
        if(nn_it->templates.empty())
          continue;
#if 1
        // TODO: there is an unwinder-related bug
        if(nn_it->templates.size()>1000)
          continue;
#endif
        for(local_SSAt::nodet::templatest::const_iterator t_it=
              nn_it->templates.begin();
            t_it!=nn_it->templates.end(); t_it++)
        {
          debug() << "Template expression: "
                  << from_expr(SSA.ns, "", *t_it) << eom;

          // check whether it is a template polyhedra or a pred abs
          std::set<symbol_exprt> symbols;
          find_symbols(*t_it, symbols);

          bool predabs=true;
          for(std::set<symbol_exprt>::iterator it=symbols.begin();
              it!=symbols.end(); it++)
          {
            std::size_t found_param=
              id2string(it->get_identifier()).find(TEMPLATE_PARAM_PREFIX);
            if(found_param!=std::string::npos)
            {
              predabs=false;
              break;
            }
          }

          // template polyhedra
          if(!predabs && t_it->id()==ID_le)
          {
            debug() << "Custom template polyhedron found" << eom;
            if(!found_poly) // create domain
            {
              domain_ptr=new tpolyhedra_domaint(
                domain_number,
                post_renaming_map,
                SSA.ns); // TODO: aux_renaming_map
              found_poly=true;
            }

            exprt expr=t_it->op0();
            bool contains_new_var=build_custom_expr(SSA, n_it, expr);
            if(contains_new_var)
              add_post_vars=true;

            static_cast<tpolyhedra_domaint *>(domain_ptr)
              ->add_template_row(
                expr,
                pre_guard,
                contains_new_var ?
                  and_exprt(pre_guard, post_guard) : post_guard,
                aux_expr,
                contains_new_var ? domaint::OUT : domaint::LOOP);
          }
          // pred abs domain
          else if(predabs)
          {
            options.set_option("predabs-solver", true);

            debug() << "Custom predicate template found" << eom;
            if(!found_predabs) // create domain
            {
              domain_ptr=new predabs_domaint(
                domain_number,
                post_renaming_map, SSA.ns); // TODO: aux_renaming_map
              found_predabs=true;
            }

            exprt expr=*t_it;
            bool contains_new_var=build_custom_expr(SSA, n_it, expr);
            if(contains_new_var)
              add_post_vars=true;

            static_cast<predabs_domaint *>(domain_ptr)
              ->add_template_row(
                expr,
                pre_guard,
                contains_new_var ?
                  and_exprt(pre_guard, post_guard) : post_guard,
                aux_expr,
                contains_new_var ? domaint::OUT : domaint::LOOP);
          }
          else // neither pred abs, nor polyhedra
          {
            warning() << "ignoring unsupported template "
                      << from_expr(SSA.ns, "", *t_it) << eom;
          }
        }
        if(add_post_vars) // for result retrieval via all_vars() only
        {
          domaint::var_specst new_var_specs(var_specs);
          var_specs.clear();
          for(domaint::var_specst::const_iterator v=new_var_specs.begin();
              v!=new_var_specs.end(); v++)
          {
            var_specs.push_back(*v);
            if(v->kind==domaint::LOOP)
            {
              var_specs.push_back(*v);
              var_specs.back().kind=domaint::OUTL;
              replace_expr(aux_renaming_map, var_specs.back().var);
            }
          }
        }
      }
    }
  }

  return (found_poly || found_predabs);
}

void template_generator_baset::instantiate_standard_domains(
  const local_SSAt &SSA)
{
  replace_mapt &renaming_map=
    std_invariants ? aux_renaming_map : post_renaming_map;

  // get domain from command line options
  if(options.get_bool_option("equalities"))
  {
    filter_equality_domain();
    domain_ptr=
      new equality_domaint(domain_number, renaming_map, var_specs, SSA.ns);
  }
  else if(options.get_bool_option("heap"))
  {
    filter_heap_domain();
    domain_ptr=new heap_domaint(domain_number, renaming_map, var_specs, SSA);
  }
  else if(options.get_bool_option("intervals"))
  {
    domain_ptr=
      new tpolyhedra_domaint(domain_number, renaming_map, SSA.ns);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_interval_template(var_specs, SSA.ns);
  }
  else if(options.get_bool_option("zones"))
  {
    domain_ptr=
      new tpolyhedra_domaint(domain_number, renaming_map, SSA.ns);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_interval_template(var_specs, SSA.ns);
  }
  else if(options.get_bool_option("octagons"))
  {
    domain_ptr=
      new tpolyhedra_domaint(domain_number, renaming_map, SSA.ns);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_sum_template(var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_interval_template(var_specs, SSA.ns);
  }
  else if(options.get_bool_option("qzones"))
  {
    domain_ptr=
      new tpolyhedra_domaint(domain_number, renaming_map, SSA.ns);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_quadratic_template(var_specs, SSA.ns);
  }
  else if(options.get_bool_option("heap-interval") ||
          options.get_bool_option("heap-zones"))
  {
    filter_heap_interval_domain();
    auto polyhedra_kind=options.get_bool_option("heap-interval")
                        ? heap_tpolyhedra_domaint::INTERVAL
                        : heap_tpolyhedra_domaint::ZONES;
    if(options.get_bool_option("sympath"))
      domain_ptr=new heap_tpolyhedra_sympath_domaint(
        domain_number, renaming_map, var_specs, SSA, polyhedra_kind);
    else
      domain_ptr=new heap_tpolyhedra_domaint(
        domain_number, renaming_map, var_specs, SSA, polyhedra_kind);
  }
}

void template_generator_baset::filter_heap_interval_domain()
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(domaint::var_specst::const_iterator v=new_var_specs.begin();
      v!=new_var_specs.end(); v++)
  {
    const domaint::vart &s=v->var;

    if(s.id()==ID_symbol && is_pointed(s) &&
       id2string(to_symbol_expr(s).get_identifier()).find(".")!=
       std::string::npos)
      continue;

    if(s.type().id()==ID_unsignedbv ||
       s.type().id()==ID_signedbv ||
       s.type().id()==ID_floatbv)
    {
      var_specs.push_back(*v);
      continue;
    }

    if(s.id()==ID_symbol && s.type().id()==ID_pointer)
    {
      // Filter out non-assigned OUT variables
      if(v->kind!=domaint::OUT ||
         ssa_inlinert::get_original_identifier(to_symbol_expr(s))!=
         to_symbol_expr(s).get_identifier())
      {
        var_specs.push_back(*v);
        continue;
      }
    }
  }
}

std::vector<exprt> template_generator_baset::collect_record_frees(
  const local_SSAt &SSA,
  local_SSAt::nodest::const_iterator loop_begin,
  local_SSAt::nodest::const_iterator loop_end)
{
  std::vector<exprt> result;
  for(auto &node : SSA.nodes)
  {
    if(node.location->location_number>loop_begin->location->location_number &&
       node.location->location_number<loop_end->location->location_number &&
       node.record_free.is_not_nil())
    {
      result.push_back(SSA.read_lhs(node.record_free, node.location));
    }
  }
  return result;
}
