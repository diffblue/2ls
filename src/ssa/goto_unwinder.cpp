/*******************************************************************\
Module: SSA Unwinder
Author: František Nečas
\*******************************************************************/

/// \file
/// SSA Unwinder

#include<stack>

#include <util/prefix.h>
#include <util/pointer_expr.h>
#include <goto-programs/remove_skip.h>
#include <goto-instrument/unwindset.h>
#include <goto-instrument/unwind.h>

#include "simplify_ssa.h"
#include "goto_unwinder.h"
#include "malloc_ssa.h"

/// Puts all unwindings corresponding to a loop into the loop itself.
/// This is done by changing the backwards goto target to the first instruction
/// of the outer-most unwind.
///
/// Such transformation is necessary for k-induction and BMC to work properly
/// and be able to prove correctness.
///
/// \note The initial state is saved so that it can be later restored.
///   This is necessary for goto_unwindt to work correctly.
void goto_local_unwindert::reconnect_loops()
{
  std::stack<goto_programt::targett> unwind_starts;
  for(auto i_it=goto_function.body.instructions.begin();
      i_it!=goto_function.body.instructions.end(); i_it++)
  {
    if(current_unwinding-i_it->get_code().get_int(unwind_flag)==0)
    {
      unwind_starts.push(i_it);
    }
    if(i_it->is_backwards_goto() && !unwind_starts.empty())
    {
      loop_targets[i_it]=i_it->get_target();
      i_it->set_target(unwind_starts.top());
      unwind_starts.pop();
    }
  }
}

std::string get_object_name(const exprt &expr)
{
  std::string name;
  const auto &obj_op=to_address_of_expr(expr).op();
  if(obj_op.id()==ID_symbol)
    name=to_symbol_expr(obj_op).get_identifier().c_str();
  else
    name=to_symbol_expr(
      to_index_expr(obj_op).array()).get_identifier().c_str();
  return name;
}

/// Recursively renames dynamic objects in the expression tree.
///
/// \param it The instruction we are currently processing
/// \param expr Subexpression to process.
/// \param rename_map Objects which have been renamed so far.
/// \pre Symbols of the previously defined dynamic objects have been cleared.
void goto_local_unwindert::rename_dynamic_objects_rec(
  goto_programt::instructiont &it,
  exprt &expr,
  std::map<std::string, std::string> &rename_map)
{
  if(expr.id()==ID_address_of)
  {
    std::string name=get_object_name(expr);
    std::string suffix="$" + std::to_string(it.location_number);
    // The form is dynamic_object$loc$<other suffixes>, keep the end suffix
    auto pos=name.find('$');
    if(pos!=std::string::npos)
    {
      auto second_pos=name.find('$', pos+1);
      if(second_pos!=std::string::npos)
        suffix+=name.substr(second_pos);
    }
    auto new_obj=dynamic_objects.create_dynamic_object(
      it,
      expr.type().subtype(),
      suffix,
      suffix.find("$co")!=std::string::npos);
    expr=new_obj.address_of(expr.type());
    rename_map[name]=get_object_name(expr);
  }
  else if(expr.id()==ID_symbol)
  {
    // Rename already renamed dynamic objects in expressions
    // This occurs in memsafety (--pointer-check) due to concrete objects
    auto &symbol_expr=to_symbol_expr(expr);
    auto rename=rename_map.find(symbol_expr.get_identifier().c_str());
    if(rename!=rename_map.end())
      symbol_expr.set_identifier(rename->second);
  }
  else if (expr.id()==ID_if && expr.get_bool("#malloc_result") &&
           to_if_expr(expr).cond().id()==ID_and)
  {
    // Update the condition for concrete object selection based on new objects
    // Its form is <nondet> && pointer_equalities, update only pointer eqs.
    auto &if_expr=to_if_expr(expr);
    // Get the object, its type and calculate new pointer equalities,
    // we do not want the new objects to be included.
    auto &obj=to_typecast_expr(if_expr.true_case()).op();
    auto pointers=collect_pointer_vars(
      goto_model.symbol_table,
      obj.type().subtype());
    // Update the objects inside true/false cases
    rename_dynamic_objects_rec(it, if_expr.true_case(), rename_map);
    rename_dynamic_objects_rec(it, if_expr.false_case(), rename_map);

    exprt::operandst pointer_equs;
    for(auto &ptr : pointers)
    {
      pointer_equs.push_back(equal_exprt(ptr, obj));
    }

    // Replace the condition
    auto &and_expr=to_and_expr(if_expr.cond());
    and_expr.op1()=not_exprt(disjunction(pointer_equs));
  }
  else
    for(auto &op : expr.operands())
      rename_dynamic_objects_rec(it, op, rename_map);
}

/// Removes all dynamic_object symbols from the symbol table.
void goto_local_unwindert::delete_dynamic_objects_from_symtable()
{
  std::vector<std::string> to_remove;
  for(const auto &symbol : goto_model.symbol_table.symbols)
    if(symbol.second.type.get_bool("#dynamic"))
      to_remove.push_back(symbol.second.name.c_str());
  for(const auto &symbol : to_remove)
    goto_model.symbol_table.remove(symbol);
}

/// Renames dynamic objects on RHS of malloc result.
////
/// Dynamic objects are hard-coded inside malloc_ssa and hence are not
/// correctly unwound (the malloc result remains the same across
/// all unwinds which is incorrect).
void goto_local_unwindert::rename_dynamic_objects()
{
  // First, we delete all the existing dynamic_object symbols, they will
  // change anyway, and we do not want any mess.
  delete_dynamic_objects_from_symtable();
  std::map<std::string, std::string> rename_map;
  for(auto &i_it : goto_function.body.instructions)
  {
    if(i_it.is_assign())
    {
      exprt &assign = i_it.assign_rhs_nonconst();
      if(assign.get_bool("#malloc_result"))
      {
        dynamic_objects.clear(i_it);
        rename_dynamic_objects_rec(i_it, assign, rename_map);
      }
    }
  }
}

/// Resets loop connections to the initial state which was valid before calling
/// \ref reconnect_loops.
/// \pre \ref reconnect_loops has been previously called, resulting in
///   \ref loop_targets map to be filled with loop configuration.
void goto_local_unwindert::reset_loop_connections()
{
  for(auto i_it=goto_function.body.instructions.begin();
      i_it!=goto_function.body.instructions.end(); i_it++)
    if(i_it->is_backwards_goto() && loop_targets.find(i_it)!=loop_targets.end())
      i_it->set_target(loop_targets.at(i_it));
  loop_targets.clear();
}

/// Marks the newly produced unwinds using an integer flag to ease
/// processing later.
/// \param before_unwind: GOTO iterator pointing before the first new unwind.
/// \param iteration_points: Iteration points as returned by goto_unwindt,
///   these mark the end of each newly produced unwind.
/// \param to_unwind: How many unwindings have been made (=the size of
///   iteration_points).
void goto_local_unwindert::mark_unwinds(
  const goto_programt::targett before_unwind,
  const std::vector<goto_programt::targett> &iteration_points,
  unsigned to_unwind)
{
  auto i_it=before_unwind;
  i_it++;
  // Start of the outermost unwind
  i_it->code_nonconst().set(unwind_flag, to_unwind);
  unsigned iteration_point=0;
  while(iteration_point<iteration_points.size())
  {
    if(i_it==iteration_points[iteration_point])
    {
      // Each iteration_point points to the last unwinding instruction
      i_it++;
      // We need to reverse the order of unwind numbers (mark the outermost
      // with the highest number).
      i_it->code_nonconst().set(unwind_flag, to_unwind-1-iteration_point);
      iteration_point++;
    }
    i_it++;
  }
}

/// Unwinds a single function up to the given bound.
/// \param to_unwind: How many more unwindings need to be made.
/// \note Since unwinding influences where the begin and end iterators point
///   to and we want to consistently mark the unwinds, we keep an iterator
///   in front of the loop (this will remain valid after unwinding).
/// \note Because GOTO unwind adds new iterations on top of the loop,
///   we need to increment the indexes (set as flags) of the already existing
///   unwindings as we go.
void goto_local_unwindert::unwind_function(
  unsigned int to_unwind)
{
  goto_unwindt unwind;
  for(auto i_it=goto_function.body.instructions.begin();
      i_it!=goto_function.body.instructions.end();)
  {
    // The new unwinds will be inserted between the existing ones and the
    // loop, update the existing unwind flags.
    int unwind_flag_value=i_it->get_code().get_int(unwind_flag);
    if(unwind_flag_value>0)
      i_it->code_nonconst().set(unwind_flag, unwind_flag_value+to_unwind);
    if(!i_it->is_backwards_goto())
    {
      i_it++;
      continue;
    }
    goto_programt::targett loop_head=i_it->get_target();
    auto loop_exit=i_it;
    loop_exit++;

    // Keep track of the first instruction before the unwind, we need to
    // process the whole block later
    auto before_unwind=loop_head;
    before_unwind--;

    // Keep loops by using CONTINUE strategy, collect iteration points
    // (end of unwinds)
    std::vector<goto_programt::targett> iteration_points;
    unwind.unwind(
      function_name,
      goto_function.body,
      loop_head,
      loop_exit,
      to_unwind,
      goto_unwindt::unwind_strategyt::CONTINUE,
      iteration_points);
    mark_unwinds(before_unwind, iteration_points, to_unwind);
    i_it=loop_exit;
  }
}

/// Unwinds the program up to the given unwinding limit in the set mode.
/// \param k: The target unwind count which should be present
///   after unwinding the loop. In the case of k-induction and BMC modes,
///   must be higher by 1 than the current unwinding. Does nothing
///   if the current unwinding is higher than the requested one.
void goto_local_unwindert::unwind(unsigned int k)
{
  if(k<=current_unwinding)
    return;
  if(!goto_function.body_available())
    return;

  unsigned to_unwind=k-current_unwinding;
  debug() << "Adding " << to_unwind << " more unwindings" << messaget::eom;
  assert(mode==unwinder_modet::NORMAL || to_unwind==1);

  if(!loop_targets.empty())
    reset_loop_connections();

  // Remove skips, there may be skips made by do-while loops which would
  // make the following loop inconsistent
  remove_skip(goto_function.body);
  unwind_function(to_unwind);

  // The unwinding generated new skips and GOTOs, update
  remove_skip(goto_function.body);
  // The update goes a bit against the concept of this class (which should
  // focus only on the one function, however there doesn't seem to be a better
  // way to support the new and the old unwinder).
  goto_model.goto_functions.update();
  current_unwinding=k;

  rename_dynamic_objects();
  split_memory_leak_assignments(goto_function.body, goto_model.symbol_table);
  goto_model.goto_functions.update();

  reconnect_loops();
  goto_model.goto_functions.update();
  recompute_ssa();
}

/// Recomputes SSA based on the newly updated GOTO and performs required
/// transformations of the SSA (see \ref update_assertions and
/// \ref add_hoisted_assertions).
void goto_local_unwindert::recompute_ssa()
{
  if(!goto_function.body_available())
    return;
  if(has_prefix(id2string(function_name), TEMPLATE_DECL))
    return;
  ssa_db.create(function_name, goto_function, goto_model.symbol_table);
  local_SSAt &SSA=ssa_db.get(function_name);
  if(simplify)
    ::simplify(SSA, SSA.ns);
  update_ssa(SSA, goto_function.body);
  // Also clear the solver, there may be left-overs with different indices
  // FIXME: This defeats the purpose of incremental solving
  ssa_db.clear_solver(function_name);
}

/// Converts assertions in an SSA node to constraints in BMC and k-induction
/// modes. Unlike assertions, constraints are pushed to the solver.
/// \param SSA The SSA that is being processed.
/// \param ssa_it SSA node where we are modifying the assertions.
/// \param loop_back SSA loop-back node of the current loop.
/// \param is_last Whether the current unwind is the last one.
void goto_local_unwindert::convert_to_constraints(
  local_SSAt &SSA,
  local_SSAt::nodest::iterator &ssa_it,
  local_SSAt::nodest::iterator &loop_back,
  bool is_last)
{
  if(!is_last)
  {
    for(const auto &a_it: ssa_it->assertions)
    {
      if(mode==unwinder_modet::K_INDUCTION)
        ssa_it->constraints.push_back(a_it);
      else if(mode==unwinder_modet::BMC)
      {
        // Must come from before the loop in order for the assertions to be
        // valid
        exprt gs=SSA.name(
          SSA.guard_symbol(),
          local_SSAt::LOOP_SELECT,
          loop_back->location);
        ssa_it->constraints.push_back(implies_exprt(not_exprt(gs), a_it));
      }
    }
    if(mode==unwinder_modet::K_INDUCTION || mode==unwinder_modet::BMC)
      ssa_it->assertions.clear();
  }
}

/// Converts assertions to constraints in the whole function.
/// Unlike assertions, constraints are pushed to the solver.
/// \param SSA: The SSA that is being processed.
/// \param goto_program: The GOTO program corresponding to the given SSA.
void goto_local_unwindert::update_assertions(
  local_SSAt &SSA,
  const goto_programt &goto_program)
{
  // Update the assertions/constraints
  // Find the loop and iterate backwards from there
  for(auto i_it=goto_program.instructions.begin();
      i_it!=goto_program.instructions.end(); i_it++)
  {
    if(!i_it->is_backwards_goto())
      continue;

    bool is_dowhile=!i_it->guard.is_true();
    auto loop_back=SSA.find_node(i_it);
    auto ssa_it=loop_back;
    int processing_unwind=1;
    while(ssa_it!=SSA.nodes.begin())
    {
      ssa_it--;
      int unwind=ssa_it->location->get_code().get_int(unwind_flag);
      if(unwind>0)
        processing_unwind=unwind+1;

      if(processing_unwind>current_unwinding)
        break;
      bool is_last=
        (is_dowhile && processing_unwind==0) || (processing_unwind<2);
      convert_to_constraints(SSA, ssa_it, loop_back, is_last);
    }
  }
}

/// Adds hoisted assertions to the SSA.
///
/// Hoisted assertions allow more precise reasoning since they make a relation
/// between assertions outside of the loops and the loop itself (which is
/// being unwound).
///
/// They take the form of <assertion is reachable> => assertion where the
/// precondition depends on the conditions to jump out of the loops.
/// We create a disjunction of exit points (mainly unwind conditions) from
/// a single loop and then a conjunction of all the loops preceding the
/// assertion.
///
/// \param SSA: The SSA that is being processed.
/// \param goto_program: The GOTO program corresponding to the given SSA.
void goto_local_unwindert::add_hoisted_assertions(
  local_SSAt &SSA,
  const goto_programt &goto_program)
{
  if(mode!=unwinder_modet::K_INDUCTION)
    return;
  // TODO: Overflow shl hack for competition mode
  exprt precondition=true_exprt();
  for(auto &it : SSA.nodes)
  {
    if(!it.assertions.empty() && !precondition.is_true())
    {
      exprt assertion=implies_exprt(precondition, conjunction(it.assertions));
      debug() << "Adding hoisted assertion: " << from_expr(assertion)
              << messaget::eom;
      it.constraints.push_back(assertion);
    }

    if(!it.location->is_backwards_goto())
      continue;
    exprt loop_precondition=false_exprt();
    int processing_unwind=0;
    for(auto loop_it=it.location->get_target(); loop_it!=it.location;loop_it++)
    {
      int unwind=loop_it->get_code().get_int(unwind_flag);
      if(unwind > 0)
        processing_unwind=unwind;
      // We are collecting gotos pointing outside the loop
      if(!loop_it->is_goto())
        continue;
      exprt g=SSA.guard_symbol(loop_it);
      exprt c=SSA.cond_symbol(loop_it);
      if(loop_it->get_target()->location_number > it.location->location_number)
      {
        if(processing_unwind>1)
          loop_precondition=or_exprt(loop_precondition, and_exprt(g, c));
      }
      else if (!loop_it->guard.is_true() && loop_it->is_backwards_goto())
      {
        // Do-while loop, the condition is IF cond GOTO upward, we care about
        // when we jump outside, hence the not
        if(processing_unwind>0)
          loop_precondition=or_exprt(loop_precondition, and_exprt(g, not_exprt(c)));
      }
    }
    if(!loop_precondition.is_false())
      precondition=and_exprt(precondition, loop_precondition);
  }
}

/// Performs necessary transformations to the SSA.
/// \param SSA: The SSA that is being processed.
/// \param goto_program: The GOTO program corresponding to the given SSA.
///
/// \note This is no-op if the program contains dynamic memory since by
///   unwinding, we introduce new dynamic objects which possibly changes the
///   semantic of the unwound assertion which goes against the concept of
///   SSA constraints.
void goto_local_unwindert::update_ssa(
  local_SSAt &SSA,
  const goto_programt &goto_program)
{
  if(dynamic_objects.have_objects())
    return;
  add_hoisted_assertions(SSA, goto_program);
  update_assertions(SSA, goto_program);
}

/// No-op, no special initialization is necessary in this unwinder, just
/// set current_unwinding to 0 to signal that we are ready.
void goto_local_unwindert::init()
{
  current_unwinding=0;
}

/// No-op, the continuation of loops is not special in any way in this unwinder,
/// the code using this method collects the guard and condition of the loop
/// on its own.
void goto_local_unwindert::loop_continuation_conditions(
  exprt::operandst &loop_cont) const
{
}

/// No-op, since we recompute the SSA every time, the indices of SSA nodes
/// change and the naming scheme from ssa_unwindert is not applicable.
/// The lack of support for this makes nontermination not work with this
/// unwinder.
void goto_local_unwindert::unwinder_rename(
  symbol_exprt &var,
  const local_SSAt::nodet &node,
  bool pre) const
{
}

void goto_unwindert::unwind_all(unsigned int k)
{
  assert(is_initialized);

  for (auto &local_unwinder : unwinder_map)
    local_unwinder.second.unwind(k);
}

void goto_unwindert::init(unwinder_modet mode)
{
  for(auto &f : goto_model.goto_functions.function_map)
  {
    unwinder_map.insert(
      {
        f.first,
        goto_local_unwindert(
          ssa_db,
          goto_model,
          f.first,
          goto_model.goto_functions.function_map.at(f.first),
          mode,
          simplify,
          dynamic_objects)});
  }
}

void goto_unwindert::init_localunwinders()
{
  for(auto &local_unwinder : unwinder_map)
    local_unwinder.second.init();
  is_initialized=true;
}
