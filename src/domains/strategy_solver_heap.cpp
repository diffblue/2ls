/*******************************************************************\

Module: Strategy solver for heap shape analysis

Author: Viktor Malik

\*******************************************************************/

// #define DEBUG_OUTPUT

#include <ssa/ssa_inliner.h>
#include "strategy_solver_heap.h"

/*******************************************************************\

Function: strategy_solver_heapt::iterate

  Inputs:

 Outputs:

 Purpose: Single iteration of invariant inference using heap shape
          domain.

\*******************************************************************/

bool strategy_solver_heapt::iterate(invariantt &_inv)
{
  heap_domaint::heap_valuet &inv=static_cast<heap_domaint::heap_valuet &>(_inv);

  bool improved=false;

  solver.new_context();

  // Entry value constraints
  exprt pre_expr=heap_domain.to_pre_constraints(inv);
#ifdef DEBUG_OUTPUT
  debug() << "pre-inv: " << from_expr(ns, "", pre_expr) << eom;
#endif
  solver << pre_expr;

  // Exit value constraints
  exprt::operandst strategy_cond_exprs;
  heap_domain.make_not_post_constraints(
    inv,
    strategy_cond_exprs,
    strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

#ifdef DEBUG_OUTPUT
  debug() << "post-inv: ";
#endif
  for(unsigned i=0; i<strategy_cond_exprs.size(); ++i)
  {
#ifdef DEBUG_OUTPUT
    debug() << (i>0 ? " || " : "")
            << from_expr(ns, "", strategy_cond_exprs[i]);
#endif
    strategy_cond_literals[i]=solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i]=literal_exprt(strategy_cond_literals[i]);
  }
#ifdef DEBUG_OUTPUT
  debug() << eom;
#endif
  solver << disjunction(strategy_cond_exprs);

#ifdef DEBUG_OUTPUT
  debug() << "solve(): ";
#endif

  if(solver()==decision_proceduret::D_SATISFIABLE)  // improvement check
  {
#ifdef DEBUG_OUTPUT
    debug() << "SAT" << eom;
#endif

#ifdef DEBUG_OUTPUT
    for(unsigned i=0; i<solver.activation_literals.size(); i++)
    {
      debug() << "literal: " << solver.activation_literals[i] << " " <<
              solver.l_get(solver.activation_literals[i]) << eom;
    }
    for(unsigned i=0; i<solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i] << " " <<
              solver.l_get(solver.formula[i]) << eom;
    }
    for(unsigned i=0; i<heap_domain.templ.size(); i++)
    {
      exprt c=heap_domain.get_row_pre_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " <<
              from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", heap_domain.templ[i].pre_guard)
              << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", heap_domain.templ[i].post_guard) << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].post_guard))
              << eom;
      exprt post=heap_domain.get_row_post_constraint(i, inv[i]);
      debug() << "post-cond: " << from_expr(ns, "", post) << " "
              << from_expr(ns, "", solver.get(post)) << eom;
      print_solver_expr(c);
      print_solver_expr(post);
    }
#endif

    for(unsigned row=0; row<strategy_cond_literals.size(); ++row)
    {
      if(solver.l_get(strategy_cond_literals[row]).is_true())
      {
        debug() << "updating row: " << row << eom;

        const heap_domaint::template_rowt &templ_row=heap_domain.templ[row];

        int actual_loc=heap_domain.get_symbol_loc(templ_row.expr);

        exprt pointer=strategy_value_exprs[row];
        exprt value=solver.get(pointer);
        // Value from the solver must be converted into an expression
        exprt ptr_value=heap_domain.value_to_ptr_exprt(value);

        exprt sym_path=get_symbolic_path(row);
        debug() << "Symbolic path: " << from_expr(ns, "", sym_path) << eom;

        if((ptr_value.id()==ID_constant &&
            to_constant_expr(ptr_value).get_value()==ID_NULL) ||
           ptr_value.id()==ID_symbol)
        {
          // Add equality p == NULL or p == symbol
          if(heap_domain.add_points_to(row, inv, sym_path, ptr_value))
          {
            improved=true;
            const std::string info=
              templ_row.mem_kind==heap_domaint::STACK ? "points to "
                                                      : "path to ";
            debug() << "Add " << info << from_expr(ns, "", ptr_value) << eom;
          }
        }
        else if(ptr_value.id()==ID_address_of)
        {
          // Template row pointer points to the heap (p = &obj)
          debug() << from_expr(ns, "", ptr_value) << eom;
          assert(ptr_value.id()==ID_address_of);
          if(to_address_of_expr(ptr_value).object().id()!=ID_symbol)
          {
            // If solver did not return address of a symbol, it is considered
            // as nondet value.
            if(heap_domain.set_nondet(row, inv, sym_path))
            {
              improved=true;
              debug() << "Set nondet" << eom;
            }
            continue;
          }

          symbol_exprt obj=to_symbol_expr(
            to_address_of_expr(ptr_value).object());

          if(obj.type()!=templ_row.expr.type() &&
             ns.follow(templ_row.expr.type().subtype())!=ns.follow(obj.type()))
          {
            // If types disagree, it's a nondet (solver assigned random value)
            if(heap_domain.set_nondet(row, inv, sym_path))
            {
              improved=true;
              debug() << "Set nondet" << eom;
            }
            continue;
          }

          // Add equality p == &obj
          if(heap_domain.add_points_to(row, inv, sym_path, obj))
          {
            improved=true;
            const std::string info=
              templ_row.mem_kind==heap_domaint::STACK ? "points to "
                                                      : "path to ";
            debug() << "Add " << info << from_expr(ns, "", obj) << eom;
          }

          // If the template row is of heap kind, we need to ensure the
          // transitive closure over the set of all paths
          if(templ_row.mem_kind==heap_domaint::HEAP &&
             obj.type().get_bool("#dynamic") &&
             id2string(obj.get_identifier()).find("$unknown")==
             std::string::npos)
          {
            // Find row with corresponding member field of the pointed object
            // (obj.member)
            int member_val_index;
            member_val_index=
              find_member_row(
                obj,
                templ_row.member,
                actual_loc,
                templ_row.kind);
            if(member_val_index>=0 &&
               !inv[member_val_index].is_nondet(sym_path))
            {
              // Add all paths from obj.next to p
              if(heap_domain.add_transitivity(
                sym_path,
                row,
                static_cast<unsigned>(member_val_index),
                inv))
              {
                improved=true;
                const std::string expr_str=
                  from_expr(ns, "", heap_domain.templ[member_val_index].expr);
                debug() << "Add all paths: " << expr_str
                        << ", through: " << from_expr(ns, "", obj) << eom;
              }
            }
          }
        }
        else
        {
          if(heap_domain.set_nondet(row, inv, sym_path))
          {
            improved=true;
            debug() << "Set nondet" << eom;
          }
        }

        // Recursively update all rows that are dependent on this row
        if(templ_row.mem_kind==heap_domaint::HEAP)
        {
          updated_rows.clear();
          if(!inv[row].is_nondet(sym_path))
            update_rows_rec(sym_path, row, inv);
        }
      }
    }
  }

  else
  {
    debug() << "UNSAT" << eom;

#ifdef DEBUG_OUTPUT
    for(unsigned i=0; i<solver.formula.size(); i++)
    {
      if(solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }

    for(unsigned i=0; i<heap_domain.templ.size(); i++)
    {
      exprt c=heap_domain.get_row_pre_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " <<
              from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", heap_domain.templ[i].pre_guard)
              << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].pre_guard))
              << eom;
      debug() << "guards: "
              << from_expr(ns, "", heap_domain.templ[i].post_guard) << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].post_guard))
              << eom;
      exprt post=heap_domain.get_row_post_constraint(i, inv[i]);
      debug() << "post-cond: " << from_expr(ns, "", post) << " "
              << from_expr(ns, "", solver.get(post)) << eom;
    }
#endif
  }
  solver.pop_context();

  return improved;
}

/*******************************************************************\

Function: strategy_solver_heapt::find_member_row

  Inputs: object
          field
          actual location

 Outputs: Row number for obj.member#loc with maximal loc less than actual_loc
          -1 if such template row does not exist

 Purpose: Find the template row that contains specified member field
          of a dynamic object at the given location.

\*******************************************************************/

int strategy_solver_heapt::find_member_row(
  const exprt &obj,
  const irep_idt &member,
  int actual_loc,
  const domaint::kindt &kind)
{
  assert(obj.id()==ID_symbol);
  std::string obj_id=id2string(
    ssa_inlinert::get_original_identifier(to_symbol_expr(obj)));

  int result=-1;
  int max_loc=-1;
  for(unsigned i=0; i<heap_domain.templ.size(); ++i)
  {
    heap_domaint::template_rowt &templ_row=heap_domain.templ[i];
    if(templ_row.kind==kind && templ_row.member==member &&
       templ_row.mem_kind==heap_domaint::HEAP)
    {
      std::string id=id2string(to_symbol_expr(templ_row.expr).get_identifier());
      if(id.find(obj_id)!=std::string::npos)
      {
        int loc=heap_domain.get_symbol_loc(templ_row.expr);
        if(loc>max_loc &&
           (kind==domaint::OUT || kind==domaint::OUTHEAP || loc<=actual_loc))
        {
          max_loc=loc;
          result=i;
        }
      }
    }
  }
  return result;
}

/*******************************************************************\

Function: strategy_solver_heapt::update_rows_rec

  Inputs:

 Outputs:

 Purpose: Recursively update rows that point to given row.

\*******************************************************************/

bool strategy_solver_heapt::update_rows_rec(
  const exprt &sym_path,
  const heap_domaint::rowt &row,
  heap_domaint::heap_valuet &value)
{
  heap_domaint::heap_row_configt &row_value=
    value[row].get_heap_config(sym_path);
  const heap_domaint::template_rowt &templ_row=heap_domain.templ[row];

  updated_rows.insert(row);
  bool result=false;
  for(const heap_domaint::rowt &ptr : row_value.pointed_by)
  {
    if(heap_domain.templ[ptr].mem_kind==heap_domaint::HEAP &&
       heap_domain.templ[ptr].member==templ_row.member)
    {
      if(heap_domain.add_transitivity(sym_path, ptr, row, value))
        result=true;

      debug() << "recursively updating row: " << ptr << eom;
      debug() << "add all paths: " << from_expr(ns, "", templ_row.expr)
              << ", through: "
              << from_expr(ns, "", templ_row.dyn_obj) << eom;
      // Recursive update is called for each row only once
      if(updated_rows.find(ptr)==updated_rows.end())
        result=update_rows_rec(sym_path, ptr, value) || result;
    }
  }
  return result;
}

/*******************************************************************\

Function: strategy_solver_heapt::print_solver_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_heapt::print_solver_expr(const exprt &expr)
{
  debug() << from_expr(ns, "", expr) << ": "
          << from_expr(ns, "", solver.get(expr)) << eom;
  forall_operands(it, expr)print_solver_expr(*it);
}

/*******************************************************************\

Function: strategy_solver_heapt::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void strategy_solver_heapt::initialize(
  const local_SSAt &SSA,
  const exprt &precondition,
  template_generator_baset &template_generator)
{
  heap_domain.initialize_domain(SSA, precondition, template_generator);

  const exprt input_bindings=heap_domain.get_input_bindings();
  if(!input_bindings.is_true())
  {
    solver << input_bindings;
    debug() << "Input bindings:" << eom;
    debug() << from_expr(ns, "", input_bindings) << eom;
  }

  if(!heap_domain.new_heap_row_specs.empty())
  {
    debug() << "New template:" << eom;
    heap_domain.output_domain(debug(), ns);
  }
}

/*******************************************************************\

Function: strategy_solver_heapt::get_symbolic_path

  Inputs:

 Outputs:

 Purpose: Get symbolic path of a model returned by the solver. A symbolic path
          is identified by evaluations of all loop guards, except the guard of
          the loop correponding to the given template row.

\*******************************************************************/
const exprt strategy_solver_heapt::get_symbolic_path(
  const heap_domaint::rowt &row)
{
  if(!heap_domain.templ[row].kind==domaint::LOOP)
    return true_exprt();

  exprt::operandst path;
  const exprt &row_loop_guard=
    to_and_expr(heap_domain.templ[row].pre_guard).op1();
  for(const exprt &guard : loop_guards)
  {
    if(guard==row_loop_guard)
      continue;

    exprt guard_value=solver.get(guard);
    assert(guard_value.is_true() || guard_value.is_false());
    if(guard_value.is_true())
      path.push_back(guard);
    else
      path.push_back(not_exprt(guard));
  }
  return conjunction(path);
}
