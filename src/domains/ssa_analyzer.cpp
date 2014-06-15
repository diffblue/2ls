/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <util/options.h>


#include "strategy_solver_base.h"
#include "strategy_solver_enumeration.h"
#include "strategy_solver_binsearch.h"
#include "ssa_analyzer.h"

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>


#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_analyzert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_analyzert::operator()(local_SSAt &SSA)
{

  if(SSA.goto_function.body.instructions.empty())
    return;


  #ifdef DEBUG
  std::cout << "ssa_analyzert::operator()" << std::endl;
  #endif

  var_listt pre_state_vars, post_state_vars;

  template_domaint::var_guardst var_guards;

  var_listt top_vars;
  add_vars(SSA.params,top_vars);
  add_vars(SSA.globals_in,top_vars);
  var_listt vars = top_vars;

  for(unsigned i=0; i<top_vars.size(); ++i) var_guards.push_back(true_exprt());

  // get all backwards edges
  forall_goto_program_instructions(i_it, SSA.goto_function.body)
  {
    if(i_it->is_backwards_goto())
    {
    
      exprt guard=SSA.guard_symbol(i_it);
      
    
      // Record the objects modified by the loop to get
      // 'primed' (post-state) and 'unprimed' (pre-state) variables.
      for(local_SSAt::objectst::const_iterator
          o_it=SSA.ssa_objects.objects.begin();
          o_it!=SSA.ssa_objects.objects.end();
          o_it++)
      {
        symbol_exprt in=SSA.name(*o_it, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.read_rhs(*o_it, i_it);
      
        var_guards.push_back(guard);
      
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
        
        std::cout << "Adding " << from_expr(ns, "", in) << " " << 
          from_expr(ns, "", out) << std::endl;        
      }
      /*
      {
        ssa_objectt guard=SSA.guard_symbol();
        symbol_exprt in=SSA.name(guard, local_SSAt::LOOP_BACK, i_it);
        symbol_exprt out=SSA.name(guard, local_SSAt::OUT, i_it);
        
        pre_state_vars.push_back(in);
        post_state_vars.push_back(out);
        var_guards.push_back(true_exprt());
      }*/
    } 
  }
  
  for(unsigned i=0; i<pre_state_vars.size(); ++i)
  {
    std::cout << from_expr(pre_state_vars[i]) << " guard " << from_expr(var_guards[i]) << std::endl;  
  }


  constraintst transition_relation;
  transition_relation << SSA;

  template_domaint::templatet templ;
   
  add_vars(pre_state_vars,vars);
  var_listt added_returns = add_vars(SSA.returns,vars);
  var_listt added_globals_out = add_vars(SSA.globals_out,vars); //TODO: guard at exit location?

for(unsigned i=0; i<added_returns.size()+added_globals_out.size(); ++i) 
    var_guards.push_back(false_exprt()); //TODO: replace this stuff
  
  if(options.get_bool_option("intervals"))
  {
    make_interval_template(templ, vars, var_guards, ns);
  }
  else if(options.get_bool_option("zones"))
  {
    make_zone_template(templ, vars, var_guards, ns); 
  }
  else if(options.get_bool_option("octagons"))
  {
    make_octagon_template(templ, vars, var_guards, ns); 
  }
  else assert(false);
    
  #ifdef DEBUG
  std::cout << "**** Template *****" << std::endl;
  std::cout << "  var size " << vars.size() << std::endl
            << "  params size " << SSA.params.size() << std::endl
            << "  pre_state " << pre_state_vars.size() << std::endl;

  #endif  
    
  template_domaint template_domain(templ);

  #ifdef DEBUG
  std::cout << "template size " << templ.size() << std::endl;
  
  template_domain.output_template(std::cout, ns);
  #endif  
    

  // solver
  //TODO: get solver from options
  satcheck_minisat_no_simplifiert satcheck;
  bv_pointerst solver(ns, satcheck);
  
  //satcheck.set_message_handler(get_message_handler());
  //solver.set_message_handler(get_message_handler()); 

  // get strategy solver from options
  strategy_solver_baset *strategy_solver;
  if(options.get_bool_option("enum-solver"))
  {
    strategy_solver = new strategy_solver_enumerationt(
      transition_relation, pre_state_vars, post_state_vars,
      template_domain, solver, ns);
  }
  else if(options.get_bool_option("binsearch-solver"))
  {
    strategy_solver = new strategy_solver_binsearcht(
      transition_relation, pre_state_vars, post_state_vars,
      template_domain, solver, ns);
  }
  /*  else if(options.get_bool_option("opt-solver"))
  {
    strategy_solver = new strategy_solver_optt(transition_relation, pre_state_vars, post_state_vars, template_domain, solver, ns);
  }*/
  else assert(false);

  iteration_number=0;


  // intialise inv
  template_domain.bottom(inv);
  template_domain.set_to_top(top_vars, inv);
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "\n"
              << "******** Forward least fixed-point iteration #"
              << iteration_number << "\n";
    #endif
   
    strategy_solver_baset::strategyt strategy;
    change = strategy_solver->improve(inv,strategy);

    if(change) 
    {
      strategy_solver->solve(inv,strategy);

      #ifdef DEBUG
      std::cout << "Value after " << iteration_number
            << " iteration(s):\n";
      template_domain.output_value(std::cout,inv,ns);
      #endif
    }
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixed-point after " << iteration_number
            << " iteration(s)\n";
  template_domain.output_value(std::cout,inv,ns);
  #endif

  delete strategy_solver;
}


exprt ssa_analyzert::get_result()
{
  assert(false);
  //  return strategy_solver.get_invariant();
}

exprt ssa_analyzert::get_result(var_listt vars) //projects on vars
{
  assert(false);
  //  return strategy_solver.get_invariant(vars);
}

bool ssa_analyzert::add_vars_filter(const symbol_exprt &s)
{
  return s.type().id()==ID_unsignedbv || s.type().id()==ID_signedbv ||
    s.type().id()==ID_floatbv;
}

ssa_analyzert::var_listt ssa_analyzert::add_vars(const local_SSAt::var_listt &vars_to_add, 
    var_listt &vars)
{
  var_listt vars_added;
  for(local_SSAt::var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
  {
    if(add_vars_filter(*it)) { vars.push_back(*it); vars_added.push_back(*it); }
  }
  return vars_added;
}

ssa_analyzert::var_listt ssa_analyzert::add_vars(const local_SSAt::var_sett &vars_to_add, 
    var_listt &vars)
{
  var_listt vars_added;
  for(local_SSAt::var_sett::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
  {
    if(add_vars_filter(*it)) { vars.push_back(*it); vars_added.push_back(*it); }
  }
  return vars_added;
}

ssa_analyzert::var_listt ssa_analyzert::add_vars(const var_listt &vars_to_add, 
    var_listt &vars)
{
  var_listt vars_added;
  for(var_listt::const_iterator it = vars_to_add.begin();
      it != vars_to_add.end(); it++)
  {
    if(add_vars_filter(*it)) { vars.push_back(*it); vars_added.push_back(*it); }
  }
  return vars_added;
}
