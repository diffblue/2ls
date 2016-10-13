/**
 *  Viktor Malik, 12.8.2016 (c).
 */

//#define DEBUG_OUTPUT

#include "strategy_solver_heap.h"
#include "../ssa/address_canonizer.h"

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
      exprt post = heap_domain.get_row_post_constraint(i, inv[i]);
      debug() << "post-cond: " << from_expr(ns, "", post) << " "
              << from_expr(ns, "", solver.get(post)) << eom;
    }
#endif

    for (unsigned row = 0; row < strategy_cond_literals.size(); ++row)
    {
      if (solver.l_get(strategy_cond_literals[row]).is_true())
      {
        debug() << "updating row: " << row << eom;

        int actual_loc = heap_domain.get_symbol_loc(heap_domain.templ[row].expr);

        exprt pointer = strategy_value_exprs[row];
        exprt value = solver.get(pointer);
        // Value from solver must be converted into expression
        exprt ptr_value = heap_domain.value_to_ptr_exprt(value);

        if (heap_domain.is_null_ptr(ptr_value))
        {
          exprt null_expr = null_pointer_exprt(to_pointer_type(ptr_value.type()));

          // Add path to NULL
          if (heap_domain.add_row_path(row, inv, null_expr,
                                       std::make_pair(nil_exprt(), nil_exprt())))
            improved = true;
          debug() << "add destination: " << from_expr(ns, "", ptr_value) << eom;

          // Add points to information
          if (heap_domain.add_points_to(row, inv, std::make_pair(null_expr, nil_exprt())))
            improved = true;
          debug() << "add points to: " << from_expr(ns, "", ptr_value) << eom;
        }
        else if (ptr_value.id() == ID_address_of)
        {
          // pointer points to the heap (p = &obj)
          debug() << from_expr(ns, "", ptr_value) << eom;
          assert(ptr_value.id() == ID_address_of);
          // Canonize address
          const exprt address = address_canonizer(ptr_value, ns);
          assert(to_address_of_expr(address).object().id() == ID_symbol);

          symbol_exprt obj = to_symbol_expr(to_address_of_expr(address).object());

          if (obj.type().get_bool("#dynamic"))
          {
            // obj is dynamic object accessed inside the function

            if (id2string(obj.get_identifier()).find("$unknown") != std::string::npos)
            { // handle unknown object
              if (heap_domain.add_points_to(row, inv, std::make_pair(obj, nil_exprt())))
                improved = true;
              debug() << "add points to: " << from_expr(ns, "", obj) << eom;
            }
            else
            {
              // Find row with corresponding member field of pointed object (obj.member)
              int member_val_index;
              if (inv[row].empty() && heap_domain.templ[row].dyn_obj.id() != ID_nil &&
                  heap_domain.get_base_name(obj) ==
                  heap_domain.get_base_name(heap_domain.templ[row].dyn_obj))
              { // for the same object find previous instance
                // (used for multiple loops in one function)
                member_val_index = find_member_row(obj, heap_domain.templ[row].member,
                                                   --actual_loc);
                if (member_val_index < 0)
                  member_val_index = find_member_row(obj, heap_domain.templ[row].member,
                                                     ++actual_loc);
              }
              else
              {
                member_val_index = find_member_row(obj, heap_domain.templ[row].member, actual_loc);
              }
              assert(member_val_index >= 0);
              exprt member_expr = heap_domain.templ[member_val_index].expr;

              // Add all paths from obj.next to p
              if (heap_domain.add_all_paths(row, (unsigned) member_val_index, inv,
                                            std::make_pair(obj, member_expr)))
                improved = true;
              debug() << "add all paths: " << from_expr(ns, "", member_expr) << ", through: "
                      << from_expr(ns, "", obj) << eom;

              // Add points to information
              if (heap_domain.add_points_to(row, inv, std::make_pair(obj, member_expr)))
                improved = true;
              debug() << "add points to: " << from_expr(ns, "", obj) << eom;

              heap_domain.add_pointed_by_row((unsigned) member_val_index, row, inv);
            }
          }
          else
          {
            // Add points to information
            if (heap_domain.add_points_to(row, inv, std::make_pair(obj, nil_exprt())))
              improved = true;
            debug() << "add points to: " << from_expr(ns, "", obj) << eom;

            // Add path to &(obj)
            if (heap_domain.add_row_path(row, inv, address_of_exprt(obj),
                                         std::make_pair(nil_exprt(), nil_exprt())))
              improved = true;
            debug() << "add destination: " << from_expr(ns, "", ptr_value) << eom;
          }
        }

        if (heap_domain.templ[row].dynamic)
        { // Recursively update all rows that are dependent on this row
          updated_rows.clear();
          update_rows_rec(row, inv);
        }
      }
    }
  }

  else
  {
#define DEBUG_OUTPUT
#ifdef DEBUG_OUTPUT
    debug() << "UNSAT" << eom;
#endif
#undef DEBUG_OUTPUT

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
 * Find the template row that contains specified member field of a dynamic object at given location.
 * Finds obj.member#loc with maximal loc less than actual_loc.
 * @param obj
 * @param member Member field to find
 * @param actual_loc Actual location number
 * @return Template row of obj.member
 */
int strategy_solver_heapt::find_member_row(const exprt &obj, const irep_idt &member, int actual_loc)
{
  assert(obj.id() == ID_symbol);
  std::string obj_id = heap_domain.get_base_name(obj);

  int result = -1;
  int max_loc = -1;
  for (unsigned i = 0; i < heap_domain.templ.size(); ++i)
  {
    heap_domaint::template_rowt &templ_row = heap_domain.templ[i];
    if (templ_row.member == member && templ_row.dynamic)
    {
      std::string id = id2string(to_symbol_expr(templ_row.expr).get_identifier());
      if (id.find(obj_id) != std::string::npos)
      {
        int loc = heap_domain.get_symbol_loc(templ_row.expr);
        if (loc <= actual_loc && loc > max_loc)
        {
          max_loc = loc;
          result = i;
        }
      }
    }
  }
  return result;
}

/**
 * Recursively update rows that point to given row.
 * @param row Pointed row
 * @param value Heap value
 * @return True if any change occured
 */
bool strategy_solver_heapt::update_rows_rec(const heap_domaint::rowt &row,
                                            heap_domaint::heap_valuet &value)
{
  updated_rows.insert(row);
  bool result = false;
  heap_domaint::template_rowt &templ_row = heap_domain.templ[row];
  for (auto &ptr : value[row].pointed_by)
  {
    if (heap_domain.add_all_paths(ptr, row, value,
                                  std::make_pair(templ_row.dyn_obj, templ_row.expr)))
      result = true;
    debug() << "recursively updating row: " << ptr << eom;
    debug() << "add all paths: " << from_expr(ns, "", templ_row.expr) << ", through: "
            << from_expr(ns, "", templ_row.dyn_obj) << eom;
    // Recursive update is called for each row only once
    if (updated_rows.find(ptr) == updated_rows.end())
      result = update_rows_rec(ptr, value) || result;
  }
  return result;
}
