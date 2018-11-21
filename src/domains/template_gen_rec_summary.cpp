/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   template_gen_rec_summary.cpp
 * Author: sarbojit
 * 
 * Created on 19 March, 2018, 10:19 PM
 */

#define SHOW_TEMPLATE
#include "tpolyhedra_domain.h"

#include "template_gen_rec_summary.h"

void template_gen_rec_summaryt::operator()(const irep_idt &function_name,
  unsigned _domain_number,
  const local_SSAt &SSA,
  exprt &merge_expr,
  bool forward)
{
  domain_number=_domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_loop(SSA, forward);
  merge_vars(function_name, SSA, merge_expr);
  
  // do not compute summary for entry-point
  if(SSA.goto_function.body.instructions.front().function!=ID__start ||
   options.get_bool_option("preconditions"))
  {
    collect_inout_vars(SSA, forward);
  }
  
  if(options.get_bool_option("context-sensitive"))
  {
    instantiate_template_for_rec(SSA);
  }
  // either use standard templates or user-supplied ones
  else if(!instantiate_custom_templates(SSA))
    instantiate_standard_domains(SSA);

#ifdef SHOW_TEMPLATE_VARIABLES
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(), var_specs, SSA.ns); debug() << eom;
#endif
#ifdef SHOW_TEMPLATE
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns);
  debug()<<"Where:\n";
  for(const exprt& op:merge_expr.operands())
  {
    debug()<<"     "<<from_expr(op)<<eom;
  }
  debug() << eom;
#endif
}

void template_gen_rec_summaryt::merge_vars(const irep_idt &function_name,
  const local_SSAt &SSA,
  exprt& merge_expr)
{
  exprt::operandst expr_vec,guards_vec;
  
  for(const exprt& var:SSA.params)
  {
    std::string var_name=
       id2string(to_symbol_expr(var).get_identifier());
    irep_idt nondet_name(var_name+"_nondet");
    in_vars_vec.push_back(symbol_exprt(dstring(var_name+"_comb"),var.type()));
    expr_vec.push_back(symbol_exprt(nondet_name,var.type()));
    
  }
  
  for(const exprt& var:SSA.globals_in)
  {
    std::string var_name=
       id2string(to_symbol_expr(var).get_identifier());
    irep_idt nondet_name(var_name+"_nondet");
    in_vars_vec.push_back(symbol_exprt(dstring(var_name+"_comb"),var.type()));
    expr_vec.push_back(symbol_exprt(nondet_name,var.type()));
    
  }
  
  for(const exprt& var:SSA.globals_out)
  {
    std::string var_name=
       id2string(to_symbol_expr(var).get_identifier());
    irep_idt nondet_name(var_name+"_nondet");
    out_vars_vec.push_back(symbol_exprt(dstring(var_name+"_comb"),var.type()));
    expr_vec.push_back(symbol_exprt(nondet_name,var.type()));
    
  }
  
  for(const local_SSAt::nodet &node:SSA.nodes)
  {
    for(const function_application_exprt &f_call:node.function_calls)
    {
      std::set<symbol_exprt> globals_in,globals_out;
      exprt guard=SSA.guard_symbol(node.location);
      std::vector<exprt>::iterator e_it=expr_vec.begin();
      if(function_name==to_symbol_expr(f_call.function()).get_identifier()&&
          f_call.function().id()==ID_symbol)
      {
        guards_vec.push_back(guard);
        if(options.get_bool_option("context-sensitive"))
        {
          for(const exprt &arg:f_call.arguments())//merging arguments
          {
            exprt& expr=*e_it;
            expr=if_exprt(guard,arg,expr);
            e_it++;
          }
        }
        SSA.get_globals(node.location,globals_in,true,false);
        for(exprt g_in:globals_in)
        {
          exprt& expr=*e_it;
          expr=if_exprt(guard,g_in,expr);
          e_it++;
        }
        SSA.get_globals(node.location,globals_out,false);
        for(exprt g_out:globals_out)
        {
          exprt& expr=*e_it;
          expr=if_exprt(guard,g_out,expr);
          e_it++;
        }
      }
    }
  }

  std::vector<exprt> exp_vec;
  guard_ins=symbol_exprt("guard#ins",bool_typet());
  for(const exprt& var:SSA.params)
  {
    std::string var_name=
       id2string(to_symbol_expr(var).get_identifier());
    irep_idt name(var_name+"#rb"),name1(var_name+"#init");
    symbol_exprt var_rb(name,var.type()),var_init(name1,var.type());
    rb_vars.push_back(var_rb);
    init_vars_map[var]=var_init;
    exprt rhs=if_exprt(guard_ins,var_rb,var_init);
    exp_vec.push_back(equal_exprt(var,rhs));
  }
  unsigned size=SSA.params.size()+SSA.globals_in.size(),n=size;
  for(unsigned i=0;i<size;i++)
  {
    exp_vec.push_back(equal_exprt(in_vars_vec.at(i),expr_vec.at(i)));
  }
  size=SSA.globals_out.size();
  for(unsigned i=0;i<size;i++)
  {
    exp_vec.push_back(equal_exprt(out_vars_vec.at(i),expr_vec.at(i+n)));
  }
  merge_expr=conjunction(exp_vec);
  merge_guard=disjunction(guards_vec);
}

void template_gen_rec_summaryt::collect_inout_vars(
  const local_SSAt &SSA,
  bool forward)
{
  // add params and globals_in
  exprt first_guard=
    SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  add_vars(
    in_vars_vec,
    merge_guard,
    and_exprt(first_guard,guard_ins),
    forward ? domaint::IN : domaint::OUT,
    var_specs);

  // add globals_out (includes return values)
  exprt last_guard=
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(
    out_vars_vec,
    merge_guard,
    last_guard,
    forward ? domaint::OUT : domaint::IN,
    var_specs);
  
  std::vector<symbol_exprt>::const_iterator v_it=rb_vars.begin();
  local_SSAt::var_sett::const_iterator out=SSA.globals_out.begin();
  for(domaint::var_spect var_spec:var_specs)
  {
    if(var_spec.kind==domaint::OUT)
    {
      post_renaming_map[var_spec.var]=*out;
      out++;
    }
    else
    {
      post_renaming_map[var_spec.var]=*v_it;
      post_renaming_map[*v_it]=var_spec.var;      
      v_it++;
    }
  }
  for(domaint::var_spect var_spec:var_specs)
  {
    if(var_spec.kind==domaint::OUT) break;
    var_spec.pre_guard=and_exprt(first_guard,guard_ins);
    var_spec.post_guard=merge_guard;
    var_spec.var=post_renaming_map[var_spec.var];
    var_specs_no_out.push_back(var_spec);
  }
}

void template_gen_rec_summaryt::instantiate_template_for_rec(local_SSAt SSA)
{
  replace_mapt &renaming_map=
    std_invariants ? aux_renaming_map : post_renaming_map;
  domain_ptr=
      new tpolyhedra_domaint(domain_number, renaming_map, SSA.ns,true);
  filter_template_domain();

  //IN templates  
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_interval_template(var_specs_no_out, SSA.ns,
                              options.get_bool_option("context-sensitive"));
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_sum_template(var_specs_no_out, SSA.ns, false);
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs_no_out, SSA.ns, false);
  //OUT templates
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_sum_template(var_specs, SSA.ns);
  static_cast<tpolyhedra_domaint *>(domain_ptr)
      ->add_difference_template(var_specs, SSA.ns);
}