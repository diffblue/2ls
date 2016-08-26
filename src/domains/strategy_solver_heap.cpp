/**
 *  Viktor Malik, 12.8.2016 (c).
 */

//#define DEBUG_OUTPUT

#include "strategy_solver_heap.h"

bool strategy_solver_heapt::iterate(invariantt &_inv)
{
  heap_domaint::heap_valuet &inv = static_cast<heap_domaint::heap_valuet &>(_inv);

  bool improved = false;

  solver.new_context();

  // Entry value constraints
  exprt pre_expr = heap_domain.to_pre_constraints(inv);
#ifdef DEBUG_OUTPUT
  debug() << "pre-inv: " << from_expr(ns, "", pre_expr) << eom;
#endif
  solver << pre_expr;

  // Exit value constraints
  exprt::operandst strategy_cond_exprs;
  heap_domain.make_not_post_constraints(inv, strategy_cond_exprs, strategy_value_exprs);

  strategy_cond_literals.resize(strategy_cond_exprs.size());

#ifdef DEBUG_OUTPUT
  debug() << "post-inv: ";
#endif
  for (unsigned i = 0; i < strategy_cond_exprs.size(); ++i)
  {
#ifdef DEBUG_OUTPUT
    debug() << (i > 0 ? " || " : "") << from_expr(ns, "", strategy_cond_exprs[i]);
#endif
    strategy_cond_literals[i] = solver.convert(strategy_cond_exprs[i]);
    strategy_cond_exprs[i] = literal_exprt(strategy_cond_literals[i]);
  }
#ifdef DEBUG_OUTPUT
  debug() << eom;
#endif
  solver << disjunction(strategy_cond_exprs);

#ifdef DEBUG_OUTPUT
  debug() << "solve(): ";
#endif

  if (solver() == decision_proceduret::D_SATISFIABLE)  // improvement check
  {
#ifdef DEBUG_OUTPUT
    debug() << "SAT" << eom;
#endif

#ifdef DEBUG_OUTPUT
    for (unsigned i = 0; i < solver.activation_literals.size(); i++)
    {
      debug() << "literal: " << solver.activation_literals[i] << " " <<
              solver.l_get(solver.activation_literals[i]) << eom;
    }
    for (unsigned i = 0; i < solver.formula.size(); i++)
    {
      debug() << "literal: " << solver.formula[i] << " " <<
              solver.l_get(solver.formula[i]) << eom;
    }
    for (unsigned i = 0; i < heap_domain.templ.size(); i++)
    {
      exprt c = heap_domain.get_row_pre_constraint(i, inv[i]);
      debug() << "cond: " << from_expr(ns, "", c) << " " <<
              from_expr(ns, "", solver.get(c)) << eom;
      debug() << "guards: " << from_expr(ns, "", heap_domain.templ[i].pre_guard) <<
              " " << from_expr(ns, "", solver.get(heap_domain.templ[i].pre_guard)) << eom;
      debug() << "guards: " << from_expr(ns, "", heap_domain.templ[i].post_guard) << " "
              << from_expr(ns, "", solver.get(heap_domain.templ[i].post_guard)) << eom;
      exprt post = heap_domain.get_row_post_constraint(i, inv[i]).op1();
      debug() << "post-cond: " << from_expr(ns, "", post) << " "
              << from_expr(ns, "", solver.get(post)) << eom;
    }
#endif

    for (unsigned row = 0; row < strategy_cond_literals.size(); ++row)
    {
      if (solver.l_get(strategy_cond_literals[row]).is_true())
      {
        debug() << "updating row: " << row << eom;
        exprt pointer = strategy_value_exprs[row];

        exprt value = solver.get(pointer);
        // Value from solver must be converted into expression
        exprt ptr_value = heap_domain.value_to_ptr_exprt(value);

        if (heap_domain.is_null_ptr(ptr_value))
        {
          exprt null_expr = null_pointer_exprt(to_pointer_type(ptr_value.type()));
          if (heap_domain.add_row_path(row, inv, null_expr,
                                       std::make_pair(nil_exprt(), nil_exprt())))
            improved = true;
          debug() << "add destination: " << from_expr(ns, "", ptr_value) << eom;

          if (heap_domain.add_points_to(row, inv, std::make_pair(null_expr, nil_exprt())))
            improved = true;
          debug() << "add points to: " << from_expr(ns, "", ptr_value) << eom;
        }
        else
        {
          // pointer points to the heap (p = &obj)
          assert(ptr_value.id() == ID_address_of);
          exprt obj = to_address_of_expr(ptr_value).object();

          // Find row with next field of pointed object (obj.next)
          int next_val_index = next_field_row(obj);
          assert(next_val_index >= 0);
          exprt next_val_expr = heap_domain.templ[next_val_index].expr;

          // Add all paths from obj.next to p
          if (heap_domain.add_all_paths(row, (unsigned) next_val_index, inv,
                                        std::make_pair(obj, next_val_expr)))
            improved = true;
          debug() << "add all paths: " << from_expr(ns, "", next_val_expr) << ", through: "
                  << from_expr(ns, "", obj) << eom;

          if (obj.type().get_bool("#dynamic"))
          { // Add points to information
            assert(obj.id() == ID_symbol);
            if (heap_domain.add_points_to(row, inv, std::make_pair(obj, next_val_expr)))
              improved = true;
            debug() << "add points to: " << from_expr(ns, "", obj) << eom;
          }
        }

        if (heap_domain.templ[row].dynamic)
        { // Recursively check all expressions and update those that point to the dynamic object
          // that this row variable belongs to.
          for (unsigned j = 0; j < heap_domain.templ.size(); ++j)
          {
            for (auto &pt : inv[j].points_to)
            {
              exprt pre_pointer = heap_domain.templ[row].expr;
              if (pre_pointer == pt.second)
              {
                if (heap_domain.add_all_paths(j, row, inv, pt))
                  improved = true;
                debug() << "recursively updating row: " << j << eom;
                debug() << "add all paths: " << from_expr(ns, "", pre_pointer) << ", through: "
                        << from_expr(ns, "", pt.first) << eom;
              }
            }
          }
        }
      }
    }
  }

  else
  {
#ifdef DEBUG_OUTPUT
    debug() << "UNSAT" << eom;
#endif

#ifdef DEBUG_OUTPUT
    for (unsigned i = 0; i < solver.formula.size(); i++)
    {
      if (solver.solver->is_in_conflict(solver.formula[i]))
        debug() << "is_in_conflict: " << solver.formula[i] << eom;
      else
        debug() << "not_in_conflict: " << solver.formula[i] << eom;
    }
#endif
  }
  solver.pop_context();

  return improved;
}

/**
 * Find the template row that contains next field of given object as row variable.
 * @param obj
 * @return Template row of obj.next
 */
int strategy_solver_heapt::next_field_row(const exprt &obj) const
{
  // Create "next" member expression
  exprt next_expr = member_exprt(obj, "next", pointer_typet(obj.type()));
  std::string next_expr_id = from_expr(ns, "", next_expr);

  int result = -1;
  for (unsigned i = 0; i < strategy_value_exprs.size(); ++i)
  { // Find the corresponding strategy value expression
    exprt val_expr = strategy_value_exprs[i];
    assert(val_expr.id() == ID_symbol);
    std::string val_expr_id = id2string(to_symbol_expr(val_expr).get_identifier());
    // Compare identifiers of row expression and "next" member expresssion
    if (val_expr_id.find(next_expr_id) != std::string::npos)
    {
      result = i;
      break;
    }
  }

  return result;
}
