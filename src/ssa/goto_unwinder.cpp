/*******************************************************************\
Module: SSA Unwinder
Author: František Nečas
\*******************************************************************/

/// \file
/// SSA Unwinder

#include<stack>

#include <goto-programs/remove_skip.h>
#include <goto-instrument/unwindset.h>
#include <goto-instrument/unwind.h>

#include "simplify_ssa.h"
#include "goto_unwinder.h"

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
      loop_targets[i_it->location_number]=i_it->get_target();
      i_it->set_target(unwind_starts.top());
      unwind_starts.pop();
    }
  }
}

/// Resets loop connections to the initial state which was valid before calling
/// \ref reconnect_loops.
/// \pre \ref reconnect_loops has been previously called, resulting in
///   \ref loop_targets map to be filled with loop configuration.
void goto_local_unwindert::reset_loop_connections()
{
  for(auto &i_it : goto_function.body.instructions)
    if(i_it.is_backwards_goto())
      i_it.set_target(loop_targets[i_it.location_number]);
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

  unsigned to_unwind=k-current_unwinding;
  debug() << "Adding " << to_unwind << " more unwindings" << messaget::eom;
  assert(mode==unwinder_modet::NORMAL || to_unwind==1);

  if(!loop_targets.empty())
    reset_loop_connections();

  // Remove skips, there may be skips made by do-while loops which would
  // make the following loop inconsistent
  remove_skip(goto_function.body);

  if (!goto_function.body_available())
    return;
  unwind_function(to_unwind);

  // The unwinding generated new skips and GOTOs, update
  remove_skip(goto_function.body);
  // The update goes a bit against the concept of this class (which should
  // focus only on the one function, however there doesn't seem to be a better
  // way to support the new and the old unwinder).
  goto_functions.update();
  current_unwinding=k;

  reconnect_loops();
  goto_functions.update();
}

/// No-op, no special initialization is necessary in this unwinder.
void goto_local_unwindert::init()
{
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
  for(auto &f : ssa_db.functions())
  {
    unwinder_map.insert(
      {
        f.first,
        goto_local_unwindert(
          ssa_db,
          goto_model.goto_functions,
          f.first,
          goto_model.goto_functions.function_map.at(f.first),
          mode,
          simplify)});
  }
}

void goto_unwindert::init_localunwinders()
{
  for(auto &local_unwinder : unwinder_map)
    local_unwinder.second.init();
  is_initialized=true;
}