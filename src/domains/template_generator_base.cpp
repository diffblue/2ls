/*******************************************************************\

Module: Template Generator Base

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Template Generator Base

#include "template_generator_base.h"

#include <util/arith_tools.h>
#include <util/find_symbols.h>
#include <util/mp_arith.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>

#include <ssa/dynamic_objects.h>
#include <ssa/ssa_inliner.h>

#include "array_domain.h"
#include "equality_domain.h"
#include "heap_domain.h"
#include "predabs_domain.h"
#include "product_domain.h"
#include "sympath_domain.h"
#include "tpolyhedra_domain.h"

#include <algorithm>

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

  post_renaming_map[lsguard]=pcond;
}

symbol_exprt template_generator_baset::get_pre_var(
  const local_SSAt &SSA,
  local_SSAt::objectst::const_iterator o_it,
  local_SSAt::nodest::const_iterator n_it)
{
  symbol_exprt pre_var=SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
  ssa_local_unwinder.unwinder_rename(pre_var, *n_it, true);

  symbol_exprt post_var=SSA.read_rhs(*o_it, n_it->location);
  ssa_local_unwinder.unwinder_rename(post_var, *n_it, false);
  post_renaming_map[pre_var]=post_var;

  rename_aux_post(post_var);
  aux_renaming_map[pre_var]=post_var;
  return pre_var;
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
  if(options.get_bool_option("arrays"))
  {
    // We need some extra renamings for the array domain. Mark them with
    // #no-loop-back so that we can later remove them from the map.
    exprt new_init_expr = init_expr;
    new_init_expr.set("#no-loop-back", true);
    post_renaming_map[new_init_expr] = phi_var;
  }
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

        if(!options.get_bool_option("competition-mode"))
        {
          if(id.find("__CPROVER_deallocated")!=std::string::npos)
          {
            auto record_frees=collect_record_frees(SSA, n_it->loophead, n_it);
            exprt::operandst d;
            for(auto &r : record_frees)
              d.push_back(equal_exprt(r, true_exprt()));
            if(!d.empty())
              obj_post_guard=and_exprt(obj_post_guard, disjunction(d));
          }
        }

        symbol_exprt pre_var=get_pre_var(SSA, o_it, n_it);

        // For fields of dynamic objects, we add two post-guards:
        // - allocation guard of the object to avoid getting values of
        //   un-allocated objects
        // - guard that the field value is not equal to the corresponding input
        //   SSA variable (with no suffix) as that variable occurs in the phi
        //   node of objects allocated inside a loop and we want to avoid
        //   getting its (random) value
        //   example: dynamic_object$0.next#ls100 != dynamic_object$0.next
        if(auto *obj = SSA.dynamic_objects.get_object_by_name(id))
        {
          obj_post_guard = and_exprt(obj_post_guard, obj->get_alloc_guard());

          exprt &post_var=post_renaming_map[pre_var];
          assert(post_var.id()==ID_symbol);
          const irep_idt orig_id=get_original_name(to_symbol_expr(post_var));
          symbol_exprt unallocated(orig_id, post_var.type());
          exprt guard=not_exprt(equal_exprt(post_var, unallocated));
          obj_post_guard=and_exprt(obj_post_guard, guard);
        }

        var_listt related_vars;
        // For arrays, we add all indices written in the same loop into
        // related variables
        if(o_it->type().id() == ID_array)
        {
          const irep_idt array_name = o_it->get_identifier();
          auto &index_domain =
            SSA.array_index_analysis[n_it->loophead->location];
          auto indices = index_domain.written_indices.find(array_name);

          if(indices != index_domain.written_indices.end())
          {
            for(auto &index_info : indices->second)
            {
              // Filter only indices written within the loop
              if(index_info.loc->location_number >=
                   n_it->loophead->location->location_number &&
                 index_info.loc->location_number <
                   n_it->location->location_number)
              {
                exprt index_expr = index_info.index;
                exprt new_index_expr = index_expr;
                replace_array_index_loop(new_index_expr, n_it, SSA, phi_nodes);
                if(new_index_expr != index_expr)
                  related_vars.push_back(new_index_expr);
              }
            }
          }
        }

        exprt init_expr;
        get_init_expr(SSA, o_it, n_it, init_expr);
        add_var(pre_var,
                pre_guard,
                obj_post_guard,
                guardst::kindt::LOOP,
                related_vars,
                n_it->location,
                all_var_specs);

#ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " " <<
          from_expr(ns, "", out) << std::endl;
#endif
      }
    }
  }
}

var_sett template_generator_baset::all_vars()
{
  var_sett vars;
  for(const auto &v : all_var_specs)
  {
    vars.insert(v.var);
  }
  return vars;
}

var_specst
template_generator_baset::filter_template_domain(const var_specst &var_specs)
{
  var_specst new_var_specs;
  for(const auto &v : var_specs)
  {
    const vart &s=v.var;

#ifdef DEBUG
    std::cout << "var: " << s << std::endl;
#endif

    if(s.id()==ID_symbol && is_pointed(s) &&
       id2string(to_symbol_expr(s).get_identifier()).find(".")!=
       std::string::npos)
      continue;


    if((s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
        s.type().id()==ID_floatbv /*|| s.type().id()==ID_c_enum_tag*/))
    {
      new_var_specs.push_back(v);
    }
  }
  return new_var_specs;
}

var_specst
template_generator_baset::filter_equality_domain(const var_specst &var_specs)
{
  var_specst new_var_specs(var_specs);
  return new_var_specs;
}

var_specst
template_generator_baset::filter_heap_domain(const var_specst &var_specs)
{
  var_specst new_var_specs;
  for(auto &var : var_specs)
  {
    if(var.var.id()==ID_symbol && var.var.type().id()==ID_pointer)
    {
      if(is_pointed(var.var) &&
         id2string(to_symbol_expr(var.var).get_identifier()).find(".")!=
         std::string::npos)
        continue;
      // Filter out non-assigned OUT variables
      if(var.guards.kind!=guardst::OUT ||
         ssa_inlinert::get_original_identifier(to_symbol_expr(var.var))!=
         to_symbol_expr(var.var).get_identifier())
        new_var_specs.push_back(var);
    }
  }
  return new_var_specs;
}

void template_generator_baset::add_var(const vart &var,
                                       const guardst::guardt &pre_guard,
                                       guardst::guardt post_guard,
                                       const guardst::kindt &kind,
                                       const var_listt &related_vars,
                                       locationt loc,
                                       var_specst &var_specs)
{
  exprt aux_expr=true_exprt();
  if(std_invariants && var.type().id() != ID_array && pre_guard.id() == ID_and)
  {
    const and_exprt &pre_guard_and=to_and_expr(pre_guard);
    exprt init_guard=and_exprt(
      pre_guard_and.op0(),
      not_exprt(pre_guard_and.op1()));
    exprt post_var=post_renaming_map[var];
    exprt aux_var=aux_renaming_map[var];
    aux_expr=and_exprt(
      implies_exprt(
        and_exprt(post_guard, not_exprt(init_guard)),
        equal_exprt(aux_var, post_var)),
      implies_exprt(init_guard, equal_exprt(aux_var, init_renaming_map[var])));
    post_guard=or_exprt(post_guard, init_guard);
  }

  var_specs.push_back(var_spect());
  var_spect &var_spec = var_specs.back();
  var_spec.guards.pre_guard = pre_guard;
  var_spec.guards.post_guard = post_guard;
  var_spec.guards.aux_expr = aux_expr;
  var_spec.guards.kind = kind;
  var_spec.var = var;
  var_spec.related_vars = related_vars;
  var_spec.loc = loc;
}

void template_generator_baset::add_vars(
  const local_SSAt::var_listt &vars_to_add,
  const guardst::guardt &pre_guard,
  const guardst::guardt &post_guard,
  const guardst::kindt &kind,
  locationt loc,
  var_specst &var_specs)
{
  for(const auto &v : vars_to_add)
    add_var(v, pre_guard, post_guard, kind, {}, loc, var_specs);
}

void template_generator_baset::add_vars(const local_SSAt::var_sett &vars_to_add,
                                        const guardst::guardt &pre_guard,
                                        const guardst::guardt &post_guard,
                                        const guardst::kindt &kind,
                                        locationt loc,
                                        var_specst &var_specs)
{
  for(const auto &v : vars_to_add)
    add_var(v, pre_guard, post_guard, kind, {}, loc, var_specs);
}

void template_generator_baset::add_vars(const var_listt &vars_to_add,
                                        const guardst::guardt &pre_guard,
                                        const guardst::guardt &post_guard,
                                        const guardst::kindt &kind,
                                        locationt loc,
                                        var_specst &var_specs)
{
  for(const auto &v : vars_to_add)
    add_var(v, pre_guard, post_guard, kind, {}, loc, var_specs);
}

void template_generator_baset::handle_special_functions(const local_SSAt &SSA)
{
  const irep_idt &function_id=SSA.function_identifier;
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
        expr=replace_map[to_typecast_expr(f.arguments()[0]).op()];
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
              domain_ptr=std::unique_ptr<domaint>(
                new tpolyhedra_domaint(
                  domain_number,
                  post_renaming_map,
                  SSA.ns,
                  options)); // TODO: aux_renaming_map
              found_poly=true;
            }

            exprt expr=to_binary_expr(*t_it).op0();
            bool contains_new_var=build_custom_expr(SSA, n_it, expr);
            if(contains_new_var)
              add_post_vars=true;

            guardst guards;
            guards.pre_guard=pre_guard;
            guards.post_guard=contains_new_var ?
                              and_exprt(pre_guard, post_guard) : post_guard;
            guards.aux_expr=aux_expr;
            guards.kind=contains_new_var ? guardst::OUT : guardst::LOOP;
            dynamic_cast<tpolyhedra_domaint *>(domain_ptr.get())
              ->add_template_row(expr, guards);
          }
            // pred abs domain
          else if(predabs)
          {
            options.set_option("predabs-solver", true);

            debug() << "Custom predicate template found" << eom;
            if(!found_predabs) // create domain
            {
              domain_ptr=std::unique_ptr<domaint>(
                new predabs_domaint(
                  domain_number,
                  post_renaming_map, SSA.ns)); // TODO: aux_renaming_map
              found_predabs=true;
            }

            exprt expr=*t_it;
            bool contains_new_var=build_custom_expr(SSA, n_it, expr);
            if(contains_new_var)
              add_post_vars=true;

            guardst guards;
            guards.pre_guard=pre_guard;
            guards.post_guard=contains_new_var ?
                              and_exprt(pre_guard, post_guard) : post_guard;
            guards.aux_expr=aux_expr;
            guards.kind=contains_new_var ? guardst::OUT : guardst::LOOP;
            dynamic_cast<predabs_domaint *>(domain_ptr.get())
              ->add_template_row(expr, guards);
          }
          else // neither pred abs, nor polyhedra
          {
            warning() << "ignoring unsupported template "
                      << from_expr(SSA.ns, "", *t_it) << eom;
          }
        }
        if(add_post_vars) // for result retrieval via all_vars() only
        {
          var_specst new_var_specs(all_var_specs);
          all_var_specs.clear();
          for(var_specst::const_iterator v=new_var_specs.begin();
              v!=new_var_specs.end(); v++)
          {
            all_var_specs.push_back(*v);
            if(v->guards.kind==guardst::LOOP)
            {
              all_var_specs.push_back(*v);
              all_var_specs.back().guards.kind = guardst::OUTL;
              replace_expr(aux_renaming_map, all_var_specs.back().var);
            }
          }
        }
      }
    }
  }

  return (found_poly || found_predabs);
}

std::unique_ptr<domaint> template_generator_baset::instantiate_standard_domains(
  const var_specst &var_specs,
  const local_SSAt &SSA,
  replace_mapt *renaming_map_)
{
  replace_mapt &renaming_map =
    renaming_map_ ? *renaming_map_
                  : std_invariants ? aux_renaming_map : post_renaming_map;

  domain_vect domains;
  // get domains from command line options
  if(options.get_bool_option("equalities"))
  {
    auto eq_var_specs = filter_equality_domain(var_specs);
    if(!eq_var_specs.empty())
      domains.emplace_back(new equality_domaint(
        domain_number++, renaming_map, eq_var_specs, SSA.ns));
  }

  if(options.get_bool_option("heap"))
  {
    auto heap_var_specs = filter_heap_domain(var_specs);
    if(!heap_var_specs.empty())
      domains.emplace_back(
        new heap_domaint(domain_number++, renaming_map, heap_var_specs, SSA));
  }

  if(options.get_bool_option("arrays"))
  {
    auto array_var_specs = filter_array_domain(var_specs);
    if(!array_var_specs.empty())
      domains.emplace_back(new array_domaint(domain_number++,
                                             post_renaming_map,
                                             init_renaming_map,
                                             array_var_specs,
                                             SSA,
                                             solver,
                                             *this));
  }

  if(options.get_bool_option("intervals"))
  {
    auto templ_var_specs = filter_template_domain(var_specs);
    if(!templ_var_specs.empty())
    {
      auto new_domain =
        new tpolyhedra_domaint(domain_number++, renaming_map, SSA.ns, options);
      new_domain->add_interval_template(templ_var_specs, SSA.ns);
      domains.emplace_back(new_domain);
    }
  }
  else if(options.get_bool_option("zones"))
  {
    auto templ_var_specs = filter_template_domain(var_specs);
    if(!templ_var_specs.empty())
    {
      auto new_domain =
        new tpolyhedra_domaint(domain_number++, renaming_map, SSA.ns, options);
      new_domain->add_difference_template(templ_var_specs, SSA.ns);
      new_domain->add_interval_template(templ_var_specs, SSA.ns);
      domains.emplace_back(new_domain);
    }
  }
  else if(options.get_bool_option("octagons"))
  {
    auto templ_var_specs = filter_template_domain(var_specs);
    if(!templ_var_specs.empty())
    {
      auto new_domain =
        new tpolyhedra_domaint(domain_number++, renaming_map, SSA.ns, options);
      new_domain->add_sum_template(templ_var_specs, SSA.ns);
      new_domain->add_difference_template(templ_var_specs, SSA.ns);
      new_domain->add_interval_template(templ_var_specs, SSA.ns);
      domains.emplace_back(new_domain);
    }
  }
  else if(options.get_bool_option("qzones"))
  {
    auto templ_var_specs = filter_template_domain(var_specs);
    if(!templ_var_specs.empty())
    {
      auto new_domain =
        new tpolyhedra_domaint(domain_number++, renaming_map, SSA.ns, options);
      new_domain->add_difference_template(templ_var_specs, SSA.ns);
      new_domain->add_quadratic_template(templ_var_specs, SSA.ns);
      domains.emplace_back(new_domain);
    }
  }

  std::unique_ptr<domaint> domain;

  // If multiple simple domains are used, use a product domain.
  if(domains.size()==1)
    domain = std::move(domains[0]);
  else
    domain = std::unique_ptr<domaint>(new product_domaint(
      domain_number++, renaming_map, SSA.ns, std::move(domains)));

  if(options.get_bool_option("sympath"))
    domain = std::unique_ptr<domaint>(new sympath_domaint(
      domain_number++, renaming_map, SSA, std::move(domain)));

  return domain;
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

var_specst
template_generator_baset::filter_array_domain(const var_specst &var_specs)
{
  var_specst new_var_specs;
  for(const auto &v : var_specs)
  {
    if(v.var.type().id() == ID_array)
      new_var_specs.push_back(v);
  }
  return new_var_specs;
}

/// Replace all variables in the given index expressions by their loop-back
/// variants if they are updated in the current loop or by their R-value variant
/// if they are not.
/// \param index Index expression
/// \param n_it Current SSA node (loop end)
/// \param SSA
/// \param phi_nodes PHI nodes for the current loop (used to check if a variable
///                  is updated within the loop)
void template_generator_baset::replace_array_index_loop(
  exprt &index,
  local_SSAt::nodest::const_iterator n_it,
  const local_SSAt &SSA,
  const ssa_domaint::phi_nodest &phi_nodes)
{
  if(index.id() == ID_symbol)
  {
    auto idx_id = to_symbol_expr(index).get_identifier();
    if(phi_nodes.find(idx_id) != phi_nodes.end())
    {
      // If the index is a symbol that is updated in the loop, we
      // have to use its loop-back variant
      symbol_exprt idx_pre_var = get_pre_var(
        SSA, SSA.ssa_objects.objects.find(ssa_objectt(index, SSA.ns)), n_it);
      index = idx_pre_var;
    }
    else
    { // Otherwise, use the RHS variant of the symbol
      index = SSA.read_rhs(index, n_it->loophead->location);
    }
  }
  else
  {
    Forall_operands(o_it, index)
      replace_array_index_loop(*o_it, n_it, SSA, phi_nodes);
  }
}
