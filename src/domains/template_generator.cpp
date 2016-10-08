/*******************************************************************\

Module: Template Generator Base

Author: Peter Schrammel

\*******************************************************************/

#include "template_generator.h"
#include "equality_domain.h"
#include "tpolyhedra_domain.h"
#include "predabs_domain.h"

#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/mp_arith.h>

#include <ssa/ssa_inliner.h>

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: template_generatort::get_pre_post_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::get_pre_post_guards(const local_SSAt &SSA,
			 local_SSAt::nodest::const_iterator n_it,
			 exprt &pre_guard, exprt &post_guard)
{
#if 0
  std::cout << "post-location: " 
	    << n_it->location->location_number << std::endl;
  assert(n_it->loophead != SSA.nodes.end());
  std::cout << "pre-location: " 
	    << n_it->loophead->location->location_number << std::endl;
#endif
  exprt lhguard = SSA.guard_symbol(n_it->loophead->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(lhguard),*n_it,true);
  exprt lsguard = SSA.name(SSA.guard_symbol(), 
			   local_SSAt::LOOP_SELECT, n_it->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(lsguard),*n_it,true);
  pre_guard = and_exprt(lhguard,lsguard);

  exprt pguard = SSA.guard_symbol(n_it->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(pguard),*n_it,false);
  exprt pcond = SSA.cond_symbol(n_it->location);
  ssa_local_unwinder.unwinder_rename(to_symbol_expr(pcond),*n_it,false);
  post_guard = and_exprt(pguard,pcond);
}

/*******************************************************************\

Function: template_generatort::get_pre_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::get_pre_var(const local_SSAt &SSA,
  		         local_SSAt::objectst::const_iterator o_it,
   		         local_SSAt::nodest::const_iterator n_it,
			 symbol_exprt &pre_var)
{
  pre_var = SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
  ssa_local_unwinder.unwinder_rename(pre_var,*n_it,true);

  symbol_exprt post_var = SSA.read_rhs(*o_it, n_it->location);
  ssa_local_unwinder.unwinder_rename(post_var,*n_it,false);
  post_renaming_map[pre_var] = post_var;

  rename_aux_post(post_var);
  aux_renaming_map[pre_var]=post_var;    
}

/*******************************************************************\

Function: template_generatort::get_init_expr

  Inputs:

 Outputs:

 Purpose: supposes that loop head PHIs are of the form 
          xphi = gls?xlb:x0

\*******************************************************************/

void template_generatort::get_init_expr(const local_SSAt &SSA,
  		         local_SSAt::objectst::const_iterator o_it,
   		         local_SSAt::nodest::const_iterator n_it,
			 exprt &init_expr)
{
  symbol_exprt phi_var = SSA.name(*o_it, local_SSAt::PHI, 
				  n_it->loophead->location);
  ssa_local_unwinder.unwinder_rename(phi_var,*n_it->loophead,true);
  for (local_SSAt::nodet::equalitiest::const_iterator e_it =
	 n_it->loophead->equalities.begin(); 
       e_it != n_it->loophead->equalities.end(); e_it++) 
  {
    if (e_it->rhs().id() == ID_if && 
        to_symbol_expr(e_it->lhs()).get_identifier()==phi_var.get_identifier()) 
    {
      const if_exprt &if_expr = to_if_expr(e_it->rhs());
      init_expr = if_expr.false_case();
      //should already be renamed for inner loops
      break;
    }
  }

  symbol_exprt pre_var = SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);
  ssa_local_unwinder.unwinder_rename(pre_var,*n_it,true);
  init_renaming_map[pre_var]=init_expr;    
}

/*******************************************************************\

Function: template_generatort::collect_variables_in

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::collect_variables_in(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA,
  bool forward)
{
  // add params and globals_in
  exprt first_guard = SSA.guard_symbol(SSA.goto_function.body.instructions.begin());
  add_vars(SSA.params,first_guard,first_guard,
           forward ? domaint::IN : domaint::OUT,
           var_specs);
  add_vars(SSA.globals_in,first_guard,first_guard,
           forward ? domaint::IN : domaint::OUT,
           var_specs);
}

/*******************************************************************\

Function: template_generatort::collect_variables_out

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::collect_variables_out(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA,
  bool forward)
{
  // add globals_out (includes return values)
  exprt last_guard = 
    SSA.guard_symbol(--SSA.goto_function.body.instructions.end());
  add_vars(SSA.globals_out,last_guard,last_guard,
	   forward ? domaint::OUT : domaint::IN,
	   var_specs);
}

/*******************************************************************\

Function: template_generatort::collect_variables_loop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::collect_variables_loop(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA,
  bool forward)
{
  // used for renaming map
  var_listt pre_state_vars, post_state_vars;

  // add loop variables
  for(local_SSAt::nodest::const_iterator n_it = SSA.nodes.begin(); 
      n_it != SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      exprt pre_guard, post_guard;
      get_pre_post_guards(SSA,n_it,pre_guard, post_guard);

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

        symbol_exprt pre_var;
        get_pre_var(SSA,o_it,n_it,pre_var);
        exprt init_expr;
        get_init_expr(SSA,o_it,n_it,init_expr);
        add_var(pre_var,pre_guard,post_guard,domaint::LOOP,var_specs);

#ifdef DEBUG
        std::cout << "Adding " << from_expr(ns, "", in) << " " << 
          from_expr(ns, "", out) << std::endl;        
#endif
      }
    } 
  }
}

/*******************************************************************\

Function: template_generatort::collect_input_variables_callingcontext

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::collect_input_variables_callingcontext(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA,    
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it)
{
  exprt guard = SSA.guard_symbol(n_it->location);

  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
  const local_SSAt &fSSA = ssa_db.get(fname);

  //getting globals at call site
  local_SSAt::var_sett cs_globals_in, globals_in;
  SSA.get_globals(n_it->location,cs_globals_in,true,false); 
  //filter out return values
  globals_in = fSSA.globals_in;

  for(local_SSAt::var_sett::iterator v_it = cs_globals_in.begin();
      v_it != cs_globals_in.end(); v_it++)
  {
    symbol_exprt dummy;
    if(ssa_inlinert::find_corresponding_symbol(*v_it,globals_in,dummy))
      add_var(*v_it,guard,guard,
	      domaint::OUT, //the same for both forward and backward
	      var_specs);
  }

  //add function arguments
  for(exprt::operandst::const_iterator a_it =  f_it->arguments().begin();
      a_it !=  f_it->arguments().end(); a_it++)
  {
    std::set<symbol_exprt> args;
    find_symbols(*a_it,args); 
    add_vars(args,guard,guard,domaint::OUT,var_specs);
  }

}

/*******************************************************************\

Function: template_generatort::collect_output_variables_callingcontext

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::collect_output_variables_callingcontext(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA,    
  local_SSAt::nodest::const_iterator n_it,
  local_SSAt::nodet::function_callst::const_iterator f_it)
{
  exprt guard = SSA.guard_symbol(n_it->location);

  assert(f_it->function().id()==ID_symbol); //no function pointers
  irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();
  const local_SSAt &fSSA = ssa_db.get(fname);

  //getting globals at call site
  local_SSAt::var_sett cs_globals_in, globals_in;
  SSA.get_globals(n_it->location,cs_globals_in,false,true,fname); 
  //with return values for function call
  globals_in = fSSA.globals_out;

  for(local_SSAt::var_sett::iterator v_it = cs_globals_in.begin();
      v_it != cs_globals_in.end(); v_it++)
  {
    symbol_exprt dummy;
    if(ssa_inlinert::find_corresponding_symbol(*v_it,globals_in,dummy))
      add_var(*v_it,guard,guard,
	      domaint::OUT, //the same for both forward and backward
	      var_specs);
  }
}

/*******************************************************************\

Function: template_generatort::filter_template_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::filter_template_domain(domaint::var_specst &var_specs)
{
  domaint::var_specst new_var_specs(var_specs);
  var_specs.clear();
  for(domaint::var_specst::const_iterator v = new_var_specs.begin(); 
      v!=new_var_specs.end(); v++)
  {
    const domaint::vart &s = v->var;

#ifdef DEBUG
    std::cout << "var: " << s << std::endl;
#endif

    if((s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
	s.type().id()==ID_floatbv /*|| s.type().id()==ID_c_enum_tag*/))
    {
      var_specs.push_back(*v);
    }
  }
}

/*******************************************************************\

Function: template_generatort::filter_equality_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::filter_equality_domain(domaint::var_specst &var_specs)
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

Function: template_generatort::add_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::add_var(const domaint::vart &var, 
			    const domaint::guardt &pre_guard, 
			    domaint::guardt post_guard,
			    const domaint::kindt &kind,
			    domaint::var_specst &var_specs)
{
  exprt aux_expr = true_exprt();
  if(std_invariants && pre_guard.id()==ID_and)
  {
    exprt init_guard = and_exprt(pre_guard.op0(),not_exprt(pre_guard.op1()));
    exprt post_var = post_renaming_map[var];
    exprt aux_var = aux_renaming_map[var];
    aux_expr = and_exprt(
      implies_exprt(and_exprt(post_guard, not_exprt(init_guard)),
			      equal_exprt(aux_var,post_var)),
      implies_exprt(init_guard,equal_exprt(aux_var,init_renaming_map[var])));
    post_guard = or_exprt(post_guard,init_guard);
  }
  if(var.type().id()!=ID_array)
  {
    var_specs.push_back(domaint::var_spect());
    domaint::var_spect &var_spec = var_specs.back();
    var_spec.pre_guard = pre_guard;
    var_spec.post_guard = post_guard;
    var_spec.aux_expr = aux_expr;
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
      var_spec.aux_expr = aux_expr;
      var_spec.kind = kind;
      var_spec.var = index_exprt(var,index);
    }
  }
}

#if 0
void template_generatort::add_vars(const local_SSAt::var_listt &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(local_SSAt::var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++) 
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}
#endif

void template_generatort::add_vars(const local_SSAt::var_sett &vars_to_add, 
			     const domaint::guardt &pre_guard, 
			     const domaint::guardt &post_guard,
			     const domaint::kindt &kind,
			     domaint::var_specst &var_specs)
{
  for(local_SSAt::var_sett::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
    add_var(*it,pre_guard,post_guard,kind,var_specs);
}

void template_generatort::add_vars(const var_listt &vars_to_add, 
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

Function: template_generatort::handle_special_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::handle_special_functions(const local_SSAt &SSA)
{
  const irep_idt &function_id = SSA.goto_function.body.instructions.front().function;
  if(id2string(function_id) == "__CPROVER_initialize")
  {
    options.set_option("intervals",true);
    options.set_option("enum-solver",true);
  }
}

/*******************************************************************\

Function: template_generatort::build_custom_expr

  Inputs:

 Outputs:

 Purpose: rename custom template to correct SSA identifiers

\*******************************************************************/

bool template_generatort::replace_post(replace_mapt replace_map, exprt &expr)
{
  bool replaced = false;
  if(expr.id()==ID_function_application)
  {
    const function_application_exprt &f = to_function_application_expr(expr);
    if(f.function().get(ID_identifier) == TEMPLATE_NEWVAR)
    {
      assert(f.arguments().size()==1);
      if(f.arguments()[0].id()==ID_typecast) 
        expr = replace_map[f.arguments()[0].op0()];
      else
        expr = replace_map[f.arguments()[0]];
      return true;
    }
  }
  for(unsigned i=0; i<expr.operands().size(); i++)
  {
    bool _replaced = replace_post(replace_map,expr.operands()[i]);
    replaced = replaced || _replaced;
  }
  return replaced;
}

bool template_generatort::build_custom_expr(const local_SSAt &SSA,
			 local_SSAt::nodest::const_iterator n_it,
			 exprt &expr)
{
  replace_mapt replace_map, replace_post_map;

  const ssa_domaint::phi_nodest &phi_nodes = 
    SSA.ssa_analysis[n_it->loophead->location].phi_nodes;
      
  for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
  {
    ssa_domaint::phi_nodest::const_iterator p_it=
      phi_nodes.find(o_it->get_identifier());

    if(p_it!=phi_nodes.end()) //modified in loop
    {
      //rename to pre
      replace_map[o_it->get_expr()] = 
        SSA.name(*o_it, local_SSAt::LOOP_BACK, n_it->location);

      //rename to post
      replace_post_map[o_it->get_expr()] = 
        SSA.read_rhs(*o_it, n_it->location);
      //TODO: unwinding
    }
    else //not modified in loop
    {
      //rename to id valid at loop head
      replace_map[o_it->get_expr()] = 
        SSA.read_rhs(*o_it,n_it->loophead->location);
      //TODO: unwinding
    }
  }

  bool contains_newvar = replace_post(replace_post_map,expr);
  replace_expr(replace_map,expr);
  return contains_newvar;
}

/*******************************************************************\

Function: template_generatort::instantiate_custom_templates

  Inputs:

 Outputs:

 Purpose: [experimental]

\*******************************************************************/

bool template_generatort::instantiate_custom_templates(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA)
{
  //TODO: the code below cannot work for unwound SSA
  //  we deactivate it for now
  return false;

#if 0
  // used for renaming map
  var_listt pre_state_vars, post_state_vars;

  bool found_poly = false, found_predabs = false;
  for(local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin(); 
      n_it!=SSA.nodes.end(); n_it++)
  {
    if(n_it->loophead != SSA.nodes.end()) //we've found a loop
    {
      exprt pre_guard, post_guard, aux_expr;
      get_pre_post_guards(SSA,n_it,pre_guard, post_guard);
      aux_expr = true_exprt(); //TODO: change to "standard" invariant semantics
      bool add_post_vars = false;

      //search for templates in the loop
      for(local_SSAt::nodest::const_iterator nn_it=n_it->loophead; 
	  nn_it!=n_it; nn_it++)
      {
	if(nn_it->templates.empty()) continue;
	if(nn_it->templates.size()>1000) continue; //TODO: there is an unwinder-related bug
	for(local_SSAt::nodet::templatest::const_iterator 
	      t_it=nn_it->templates.begin(); 
	    t_it!=nn_it->templates.end(); t_it++)
	{
	  debug() << "Template expression: " 
		  << from_expr(SSA.ns,"",*t_it) << eom;

	  // check whether it is a template polyhedra or a pred abs
	  std::set<symbol_exprt> symbols;
	  find_symbols(*t_it, symbols);

	  bool predabs = true;
	  for(std::set<symbol_exprt>::iterator it = symbols.begin();
	      it != symbols.end(); it++)
	  {
	    std::size_t found_param = 
	      id2string(it->get_identifier()).find(TEMPLATE_PARAM_PREFIX);
	    if (found_param != std::string::npos)
	    {              
	      predabs = false;
	      break;
	    }
	  }

	  //template polyhedra
	  if(!predabs && t_it->id()==ID_le)
	  {
	    debug() << "Custom template polyhedron found" << eom;
	    if(!found_poly) //create domain
	    {
	      domain_ptr = new tpolyhedra_domaint(domain_number,
		post_renaming_map); //TODO: aux_renaming_map
	      found_poly = true;
	    }
	    exprt expr = t_it->op0();
	    bool contains_new_var = build_custom_expr(SSA,n_it,expr);
	    if(contains_new_var) add_post_vars = true;
	    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_template_row(
		expr,pre_guard,
		contains_new_var ? and_exprt(pre_guard,post_guard) : post_guard,
		aux_expr,
		contains_new_var ? domaint::OUT : domaint::LOOP);
	  }
	  // pred abs domain
	  else if (predabs) 
	  {
	    options.set_option("predabs-solver",true);

	    debug() << "Custom predicate template found" << eom;
	    if(!found_predabs) //create domain
	    {
	      domain_ptr = new predabs_domaint(domain_number,
		post_renaming_map); //TODO: aux_renaming_map
	      found_predabs = true;
	    }
	    exprt expr = *t_it;
	    bool contains_new_var = build_custom_expr(SSA,n_it,expr);
	    if(contains_new_var) add_post_vars = true;
	    static_cast<predabs_domaint *>(domain_ptr)->add_template_row(
		expr,pre_guard,
		contains_new_var ? and_exprt(pre_guard,post_guard) : post_guard,
		aux_expr,
		contains_new_var ? domaint::OUT : domaint::LOOP);
		  
	  }
	  else // neither pred abs, nor polyhedra
	    warning() << "ignoring unsupported template " 
		      << from_expr(SSA.ns,"",*t_it) << eom;
	}
	if(add_post_vars) //for result retrieval via all_vars() only
	{
	  domaint::var_specst new_var_specs(var_specs);
	  var_specs.clear();
	  for(domaint::var_specst::const_iterator v = new_var_specs.begin(); 
	      v!=new_var_specs.end(); v++)
	  {
	    var_specs.push_back(*v);
	    if(v->kind==domaint::LOOP)
	    {
	      var_specs.push_back(*v);
	      var_specs.back().kind = domaint::OUTL;
              replace_expr(aux_renaming_map,var_specs.back().var);
	    }
	  }
	}
      }
    }
  }

  return (found_poly || found_predabs);
#endif
}

/*******************************************************************\

Function: template_generatort::instantiate_standard_domains

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void template_generatort::instantiate_standard_domains(
  domaint::var_specst &var_specs,
  const local_SSAt &SSA)
{
  replace_mapt &renaming_map =
    std_invariants ? aux_renaming_map : post_renaming_map;
  
  //get domain from command line options
  if(options.get_bool_option("equalities"))
  {
    filter_equality_domain(var_specs);
    domain_ptr = new equality_domaint(domain_number,
				      renaming_map, var_specs, SSA.ns);
  }
  else if(options.get_bool_option("intervals"))
  {
    domain_ptr = new tpolyhedra_domaint(domain_number,
					renaming_map);
    filter_template_domain(var_specs);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_interval_template(
      var_specs, SSA.ns);
  }
  else if(options.get_bool_option("zones"))
  {
    domain_ptr = new tpolyhedra_domaint(domain_number,
					renaming_map);
    filter_template_domain(var_specs);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_difference_template(
      var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_interval_template(
      var_specs, SSA.ns);
  }
  else if(options.get_bool_option("octagons"))
  {
    domain_ptr = new tpolyhedra_domaint(domain_number,
					renaming_map);
    filter_template_domain(var_specs);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_sum_template(
      var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_difference_template(
      var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_interval_template(
      var_specs, SSA.ns);
  }
  else if(options.get_bool_option("qzones"))
  {
    domain_ptr = new tpolyhedra_domaint(domain_number,
					renaming_map);
    filter_template_domain(var_specs);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_difference_template(
      var_specs, SSA.ns);
    static_cast<tpolyhedra_domaint *>(domain_ptr)->add_quadratic_template(
      var_specs, SSA.ns);
  }
}
