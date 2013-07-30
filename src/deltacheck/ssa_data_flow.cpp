/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#include <util/decision_procedure.h>

#include "ssa_data_flow.h"
#include "solver.h"

#ifdef DEBUG
#include <iostream>
#endif

/*******************************************************************\

Function: ssa_data_flowt::get_backwards_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::tie_inputs_together(decision_proceduret &dest)
{
  // the following are inputs:
  // 1) the parameters of the functions
  // 2) any global objects mentioned
  // 3) the guard at the entry point

  if(function_SSA_old.goto_function.body.empty() ||
     function_SSA_new.goto_function.body.empty())
    return;
    
  goto_programt::const_targett l_old=
    function_SSA_old.goto_function.body.instructions.begin();

  goto_programt::const_targett l_new=
    function_SSA_new.goto_function.body.instructions.begin();
    
  // 1) parameters
  
  const code_typet::parameterst &p_new=
    function_SSA_new.goto_function.type.parameters();
    
  const code_typet::parameterst &p_old=
    function_SSA_old.goto_function.type.parameters();

  for(unsigned p=0; p<p_new.size(); p++)
    if(p<p_old.size() &&
       p_old[p].type()==p_new[p].type())
    {
      symbol_exprt s_old(p_old[p].get_identifier(), p_old[p].type());
      symbol_exprt s_new(p_new[p].get_identifier(), p_new[p].type());
      s_old=function_SSA_old.read_rhs(s_old, l_old);
      s_new=function_SSA_new.read_rhs(s_new, l_new);

      dest.set_to_true(equal_exprt(s_old, s_new));
    }
    
  // 2) globals
  
  for(function_SSAt::objectst::const_iterator
      it=function_SSA_new.objects.begin();
      it!=function_SSA_new.objects.end();
      it++)
  {
    const symbol_exprt &s=to_symbol_expr(*it);
    const symbolt &symbol=ns.lookup(s);
    if(!symbol.is_static_lifetime || !symbol.is_lvalue) continue;
    if(function_SSA_old.objects.find(s)==
       function_SSA_old.objects.end()) continue;
    
    symbol_exprt s_new=function_SSA_new.read_rhs(s, l_new);
    symbol_exprt s_old=function_SSA_old.read_rhs(s, l_old);

    dest.set_to_true(equal_exprt(s_old, s_new));
  }

  // 3) guard
  dest.set_to_true(
    equal_exprt(function_SSA_old.guard_symbol(l_old),
                function_SSA_new.guard_symbol(l_new)));
}

/*******************************************************************\

Function: ssa_data_flowt::get_backwards_edge

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ssa_data_flowt::backwards_edget ssa_data_flowt::backwards_edge(
  const function_SSAt &function_SSA,
  locationt from)
{
  assert(from->is_backwards_goto());

  backwards_edget result;

  result.from=from;
  result.to=from->get_target();

  for(function_SSAt::objectst::const_iterator
      o_it=function_SSA.objects.begin();
      o_it!=function_SSA.objects.end();
      o_it++)
  {
    symbol_exprt in=function_SSA.read_in(*o_it, result.to);
    symbol_exprt out=function_SSA.read_rhs(*o_it, result.from);
  
    result.pre_predicate.vars.push_back(in);
    result.post_predicate.vars.push_back(out);
  }

  symbol_exprt guard=function_SSA.guard_symbol();
  result.pre_predicate.guard=function_SSA.name(guard, function_SSAt::LOOP, result.to);
  result.post_predicate.guard=function_SSA.name(guard, function_SSAt::OUT, result.from);

  // Initially, we start with the strongest invariant: false
  // This gets weakened incrementally.
  result.pre_predicate.make_false();

  return result;  
}

/*******************************************************************\

Function: ssa_data_flowt::get_backwards_edges

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::get_backwards_edges()
{
  // old program
  forall_goto_program_instructions(i_it, function_SSA_old.goto_function.body)
  {
    if(i_it->is_backwards_goto())
      backwards_edges.push_back(backwards_edge(function_SSA_old, i_it));
  }
  
  // new program
  forall_goto_program_instructions(i_it, function_SSA_new.goto_function.body)
  {
    if(i_it->is_backwards_goto())
      backwards_edges.push_back(backwards_edge(function_SSA_new, i_it));
  }
}

/*******************************************************************\

Function: ssa_data_flowt::fixed_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::fixed_point()
{
  get_backwards_edges();
  setup_properties();

  iteration_number=0;
  
  bool change;

  do
  {
    iteration_number++;
    
    #ifdef DEBUG
    std::cout << "Iteration #" << iteration_number << "\n";
    print_invariant(std::cout);
    #endif
   
    change=iteration();
  }
  while(change);

  #ifdef DEBUG
  std::cout << "Fixedpoint after " << iteration_number
            << " iteration(s)\n";
  print_invariant(std::cout);
  #endif

  // we check the properties once we have the fixed point
  check_properties();
}

/*******************************************************************\

Function: ssa_data_flowt::iteration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ssa_data_flowt::iteration()
{
  solvert solver(ns);

  // feed SSA(s) into solver
  solver << function_SSA_new;

  if(use_old)
  {
    solver << function_SSA_old;
    tie_inputs_together(solver);
  }

  // feed in current pre-state predicates
  for(backwards_edgest::const_iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
    b_it->pre_predicate.set_to_true(solver);
  
  // feed in assertions to aid fixed-point computation
  for(propertiest::const_iterator
      p_it=properties.begin(); p_it!=properties.end(); p_it++)
    solver.add_expression(p_it->condition);

  // solve
  solver.dec_solve();
 
  #ifdef DEBUG
  std::cout << "=======================\n";
  solver.print_assignment(std::cout);
  std::cout << "=======================\n";
  #endif

  // now get new value of post-state predicates
  for(backwards_edgest::iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
    b_it->post_predicate.get(solver);

  // now 'OR' with previous pre-state predicates

  bool change=false;

  for(backwards_edgest::iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
  {
    // copy
    predicatet tmp=b_it->post_predicate;
    
    // rename
    tmp.rename(b_it->pre_predicate.guard, b_it->pre_predicate.vars);
    
    #if 0
    tmp.output(std::cout);
    #endif
    
    // make disjunction
    if(b_it->pre_predicate.disjunction(tmp))
      change=true;
  }
  
  return change;
}

/*******************************************************************\

Function: ssa_data_flowt::check_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::check_properties()
{
  for(propertiest::iterator
      p_it=properties.begin(); p_it!=properties.end(); p_it++)
  {
    solvert solver(ns);

    // feed SSA into solver
    solver << function_SSA_new;
    
    if(use_old)
    {
      solver << function_SSA_old;
      tie_inputs_together(solver);
    }

    // feed in current fixed-point
    for(backwards_edgest::const_iterator
        b_it=backwards_edges.begin();
        b_it!=backwards_edges.end();
        b_it++)
      b_it->pre_predicate.set_to_true(solver);

    #ifdef DEBUG
    std::cout << "GUARD: " << from_expr(ns, "", p_it->guard) << "\n";
    std::cout << "CHECKING: " << from_expr(ns, "", p_it->condition) << "\n";
    #endif
    
    // feed in the assertion
    solver.set_to_true(p_it->guard);
    solver.set_to_false(p_it->condition);

    // solve
    decision_proceduret::resultt result=solver.dec_solve();
   
    #ifdef DEBUG
    std::cout << "=======================\n";
    solver.print_assignment(std::cout);
    std::cout << "=======================\n";
    #endif

    tvt status;
    
    if(result==decision_proceduret::D_UNSATISFIABLE)
      status=tvt(true);
    else if(result==decision_proceduret::D_SATISFIABLE)
    {
      status=tvt(false);
      generate_countermodel(*p_it, solver);
    }
    else
      status=tvt::unknown();

    p_it->status=status;
    
    #ifdef DEBUG
    std::cout << "RESULT: " << status << "\n";
    std::cout << "\n";
    #endif
  }
}

/*******************************************************************\

Function: ssa_data_flowt::countermodel_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::countermodel_expr(
  const exprt &src,
  std::set<exprt> &dest)
{
  forall_operands(it, src)
    countermodel_expr(*it, dest);
  
  if(src.id()==ID_symbol)
    dest.insert(src);
}

/*******************************************************************\

Function: ssa_data_flowt::generate_countermodel

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::generate_countermodel(
  propertyt &property,
  const decision_proceduret &solver)
{
  // collect all expressions from SSA that seem interesting
  
  std::set<exprt> expressions;
  
  for(function_SSAt::nodest::const_iterator
      n_it=function_SSA_new.nodes.begin();
      n_it!=function_SSA_new.nodes.end();
      n_it++)
  {
    const function_SSAt::nodet &node=n_it->second;
    for(function_SSAt::nodet::equalitiest::const_iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      countermodel_expr(e_it->lhs(), expressions);
      countermodel_expr(e_it->rhs(), expressions);
    }

    for(function_SSAt::nodet::constraintst::const_iterator
        e_it=node.constraints.begin();
        e_it!=node.constraints.end();
        e_it++)
    {
      countermodel_expr(*e_it, expressions);
    }
  }
  
  if(use_old)
  {
    for(function_SSAt::nodest::const_iterator
        n_it=function_SSA_old.nodes.begin();
        n_it!=function_SSA_old.nodes.end();
        n_it++)
    {
      const function_SSAt::nodet &node=n_it->second;
      for(function_SSAt::nodet::equalitiest::const_iterator
          e_it=node.equalities.begin();
          e_it!=node.equalities.end();
          e_it++)
      {
        countermodel_expr(e_it->lhs(), expressions);
        countermodel_expr(e_it->rhs(), expressions);
      }

      for(function_SSAt::nodet::constraintst::const_iterator
          e_it=node.constraints.begin();
          e_it!=node.constraints.end();
          e_it++)
      {
        countermodel_expr(*e_it, expressions);
      }
    }
  }
  
  // now collect from property
  countermodel_expr(property.guard, expressions);
  countermodel_expr(property.condition, expressions);

  // get values for those expressions
  for(std::set<exprt>::const_iterator
      e_it=expressions.begin();
      e_it!=expressions.end();
      e_it++)
  {
    exprt value=solver.get(*e_it);
    if(value.is_not_nil())
      property.value_map[*e_it]=value;
  }
}

/*******************************************************************\

Function: ssa_data_flowt::setup_properties

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::setup_properties()
{
  forall_goto_program_instructions(i_it, function_SSA_new.goto_function.body)
  {
    if(i_it->is_assert())
    {
      properties.push_back(propertyt());
      properties.back().loc=i_it;
      properties.back().condition=function_SSA_new.read_rhs(i_it->guard, i_it);
      properties.back().guard=function_SSA_new.guard_symbol(i_it);
    }
  }
}

/*******************************************************************\

Function: ssa_data_flowt::print_invariant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_data_flowt::print_invariant(std::ostream &out) const
{
  for(backwards_edgest::const_iterator
      b_it=backwards_edges.begin();
      b_it!=backwards_edges.end();
      b_it++)
  {
    const backwards_edget &be=*b_it;
  
    out << "*** From " << be.from->location_number
        << " to " << be.to->location_number << "\n";

    out << "Pre: ";
    for(predicatet::var_listt::const_iterator
        v_it=be.pre_predicate.vars.begin();
        v_it!=be.pre_predicate.vars.end(); v_it++)
      out << " " << v_it->get_identifier();
    out << "\n";
    out << "GSym: " << be.pre_predicate.guard.get_identifier()
        << "\n";

    out << "Post:";
    for(predicatet::var_listt::const_iterator
        v_it=be.post_predicate.vars.begin();
        v_it!=be.post_predicate.vars.end(); v_it++)
      out << " " << v_it->get_identifier();
    out << "\n";
    out << "GSym: " << be.post_predicate.guard.get_identifier()
        << "\n";
    
    out << be.pre_predicate;

    out << "\n";
  }
}
