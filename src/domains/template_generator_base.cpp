/*******************************************************************\

Module: Template Generator Base

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator_base.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/mp_arith.h>

#ifdef DEBUG
#include <iostream>
#endif


/*******************************************************************\

Function: template_generator_baset::collect_variables_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_baset::collect_variables_loop(const local_SSAt &SSA,bool forward)
{
  // used for renaming map
  var_listt pre_state_vars, post_state_vars;

  // add loop variables
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin(); 
      n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      exprt lhguard = SSA.guard_symbol(n_it->loophead->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lhguard),*n_it,true);
      exprt lsguard = SSA.name(SSA.guard_symbol(), local_SSAt::LOOP_SELECT, n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard),*n_it,true);
      exprt pre_guard = and_exprt(lhguard,lsguard);

      exprt pguard = SSA.guard_symbol(n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(pguard),*n_it,false);
      exprt pcond = SSA.cond_symbol(n_it->location);
      ssa_local_unwinder.unwinder_rename(to_symbol_expr(pcond),*n_it,false);
      exprt post_guard = and_exprt(pguard,pcond);
      
      const ssa_domaint::phi_nodest &phi_nodes = 
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

	if(p_it==phi_nodes.end()) continue; // object not modified in this loop

        symbol_exprt in=SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
        ssa_local_unwinder.unwinder_rename(in,*n_it,true);
        symbol_exprt out=SSA.read_rhs(*o_it, n_it->location);
        ssa_local_unwinder.unwinder_rename(out,*n_it,false);

        add_var(in,pre_guard,post_guard,domaint::LOOP,var_specs);
      
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
        
  #ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " " << 
          from_expr(ns, "", out) << std::endl;        
  #endif
     }

      /*
      // local nondet variables
      const ssa_domaint &ssa_domain=SSA.ssa_analysis[i_it->get_target()];
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        ssa_domaint::def_mapt::const_iterator 
          d_it = ssa_domain.def_map.find(o_it->get_identifier());
	if(d_it!=ssa_domain.def_map.end()) 
	{
  #if 1
        std::cout << "ssa_object " << o_it->get_identifier() <<
		  ": " << d_it->second.def.is_input() << std::endl;        
  #endif
	  symbol_exprt in=SSA.name_input(*o_it);
          exprt guard = SSA.guard_symbol(i_it->get_target());
	  add_var(in,guard,guard,domaint::IN,var_specs);

  #if 1
          std::cout << "Adding " << from_expr(ns, "", in) << std::endl;        
  #endif
	}
      }
      */
    } 
  }
  
  // building map for renaming from pre into post-state
  assert(pre_state_vars.size()==post_state_vars.size());
  var_listt::const_iterator it1=pre_state_vars.begin();
  var_listt::const_iterator it2=post_state_vars.begin();
  for(; it1!=pre_state_vars.end(); ++it1, ++it2)
  {
    renaming_map[*it1]=*it2;    
  }
}

/*******************************************************************\

Function: template_generator_baset::all_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

domaint::var_sett template_generator_baset::all_vars()
{
  domaint::var_sett vars;
  for(domaint::var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
  {
    vars.insert(v->var);
  }
  return vars;
}

/*******************************************************************\

Function: template_generator_baset::filter_template_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_baset::filter_template_domain()
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(domaint::var_specst::const_iterator v = new_var_specs.begin(); 
      v!=new_var_specs.end(); v++)
  {
    const domaint::vart &s = v->var;
    std::cout << "var: " << s << std::endl;
    if((s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
	s.type().id()==ID_floatbv /*|| s.type().id()==ID_c_enum_tag*/))
    {
      var_specs.push_back(*v);
    }
  }
}

/*******************************************************************\

Function: template_generator_baset::filter_equality_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_baset::filter_equality_domain()
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(domaint::var_specst::const_iterator v = new_var_specs.begin(); 
      v!=new_var_specs.end(); v++)
  {
    var_specs.push_back(*v);
  }
}

/*******************************************************************\

Function: template_generator_baset::add_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_baset::add_var(const domaint::vart &var, 
			    const domaint::guardt &pre_guard, 
			    const domaint::guardt &post_guard,
			    const domaint::kindt &kind,
			    domaint::var_specst &var_specs)
{
  if(var.type().id()!=ID_array)
  {
    var_specs.push_back(domaint::var_spect());
    domaint::var_spect &var_spec = var_specs.back();
    var_spec.pre_guard = pre_guard;
    var_spec.post_guard = post_guard;
    var_spec.kind = kind;
    var_spec.var = var;
  }

  //arrays
  if(var.type().id()==ID_array && options.get_bool_option("arrays"))
  {
    const array_typet &array_type = to_array_type(var.type());
    mp_integer size;
    to_integer(array_type.size(), size);
    for(mp_integer i=0; i<size; i=i+1) 
    {
      var_specs.push_back(domaint::var_spect());
      domaint::var_spect &var_spec = var_specs.back();
      constant_exprt index = from_integer(i,array_type.size().type());
      var_spec.pre_guard = pre_guard;
      var_spec.post_guard = post_guard;
      var_spec.kind = kind;
      var_spec.var = index_exprt(var,index);
    }
  }
}

void template_generator_baset::add_vars(const local_SSAt::var_listt &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(local_SSAt::var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++) 
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}

void template_generator_baset::add_vars(const local_SSAt::var_sett &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(local_SSAt::var_sett::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}

void template_generator_baset::add_vars(const var_listt &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}

/*******************************************************************\

Function: template_generator_baset::handle_special_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_baset::handle_special_functions(const local_SSAt &SSA)
{
  const irep_idt &function_id = SSA.goto_function.body.instructions.front().function;
  if(id2string(function_id) == "c::__CPROVER_initialize")
  {
    options.set_option("intervals",true);
    options.set_option("enum-solver",true);
  }
}

/*******************************************************************\

Function: template_generator_baset::instantiate_standard_domains

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generator_baset::instantiate_standard_domains(const local_SSAt &SSA)
{
  //get domain from command line options
  if(options.get_bool_option("equalities"))
  {
    filter_equality_domain();
    domain_ptr = new equality_domaint(renaming_map, var_specs, SSA.ns);
  }
  else if(options.get_bool_option("intervals"))
  {
    domain_ptr = new tpolyhedra_domaint(renaming_map);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_interval_template(
      var_specs, SSA.ns);
  }
  else if(options.get_bool_option("zones"))
  {
    domain_ptr = new tpolyhedra_domaint(renaming_map);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_zone_template(
      var_specs, SSA.ns);
  }
  else if(options.get_bool_option("octagons"))
  {
    domain_ptr = new tpolyhedra_domaint(renaming_map);
    filter_template_domain();
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_octagon_template(
      var_specs, SSA.ns);
  }
}
