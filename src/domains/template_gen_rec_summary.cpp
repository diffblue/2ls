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
  const local_SSAt &SSA, tmpl_rename_mapt &templ_maps,
  bool forward, bool recursive)
{
  domain_number=_domain_number;
  handle_special_functions(SSA); // we have to call that to prevent trouble!

  collect_variables_loop(SSA, forward);
  
  // do not compute summary for entry-point
  if(SSA.goto_function.body.instructions.front().function!=ID__start ||
   options.get_bool_option("preconditions"))
  {
    collect_variables_inout(SSA, forward);
  }
  if(recursive) get_renaming_maps(function_name,SSA,templ_maps);
  // either use standard templates or user-supplied ones
  if(!instantiate_custom_templates(SSA))
    instantiate_standard_domains(SSA,recursive);

#ifdef SHOW_TEMPLATE_VARIABLES
  debug() << "Template variables: " << eom;
  domaint::output_var_specs(debug(), var_specs, SSA.ns); debug() << eom;
#endif
#ifdef SHOW_TEMPLATE
  debug() << "Template: " << eom;
  domain_ptr->output_domain(debug(), SSA.ns); debug() << eom;
#endif
}

void template_gen_rec_summaryt::get_renaming_maps(const irep_idt &function_name,
 local_SSAt SSA,tmpl_rename_mapt &templ_maps)
{
  for(local_SSAt::nodet node:SSA.nodes)
    for(function_application_exprt f_call:node.function_calls)
      if(function_name==to_symbol_expr(f_call.function()).get_identifier())
      {
        std::pair<exprt,std::vector<exprt>> p(SSA.guard_symbol(node.location),
         std::vector<exprt>(f_call.arguments()));
        std::set<symbol_exprt> globals_in,globals_out;
        SSA.get_globals(node.location,globals_in);
        for(exprt e:globals_in) {p.second.push_back(e);}
        SSA.get_globals(node.location,globals_out,false);
        for(exprt e:globals_out) {p.second.push_back(e);}
        for(domaint::var_spect s:var_specs) {std::cout<<from_expr(s.var)<<"\n";}////
        for(exprt expr:p.second) {std::cout<<from_expr(expr)<<"\n";}////
        //assert(p.second.size()==var_specs.size());
        templ_maps.push_back(p);
      }
}