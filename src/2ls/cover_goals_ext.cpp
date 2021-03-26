/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Cover a set of goals incrementally

#include <util/threeval.h>
#include <solvers/prop/literal_expr.h>

#include <ssa/ssa_build_goto_trace.h>

#include "cover_goals_ext.h"

cover_goals_extt::~cover_goals_extt()
{
}

/// Mark goals that are covered
void cover_goals_extt::mark()
{
  for(std::list<cover_goalt>::iterator
        g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered &&
       solver.l_get(g_it->condition).is_true())
    {
      g_it->covered=true;
      _number_covered++;
    }
}

/// Build clause
void cover_goals_extt::constraint()
{
  exprt::operandst disjuncts;

  for(std::list<cover_goalt>::const_iterator
        g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->covered && !g_it->condition.is_false())
      disjuncts.push_back(literal_exprt(g_it->condition));

  // this is 'false' if there are no disjuncts
  solver << disjunction(disjuncts);
}

/// Build clause
void cover_goals_extt::freeze_goal_variables()
{
  for(std::list<cover_goalt>::const_iterator
        g_it=goals.begin();
      g_it!=goals.end();
      g_it++)
    if(!g_it->condition.is_constant())
      solver.solver->set_frozen(g_it->condition);
}

/// Try to cover all goals
void cover_goals_extt::operator()()
{
  _iterations=_number_covered=0;

  decision_proceduret::resultt dec_result;

  // We use incremental solving, so need to freeze some variables
  // to prevent them from being eliminated.
  freeze_goal_variables();

  do
  {
    // We want (at least) one of the remaining goals, please!
    _iterations++;

    constraint();

    dec_result=solver();

    switch(dec_result)
    {
    case decision_proceduret::resultt::D_UNSATISFIABLE: // DONE
      break;

    case decision_proceduret::resultt::D_SATISFIABLE:
      // mark the goals we got
      mark();

      // notify
      assignment();

      if(!all_properties)
        return; // exit on first failure if requested
      break;

    default:
      error() << "decision procedure has failed" << eom;
      return;
    }
  }
  while(dec_result==decision_proceduret::resultt::D_SATISFIABLE &&
        number_covered()<size());
}

/// checks whether a countermodel is spurious
void cover_goals_extt::assignment()
{
  // check loop head choices in model
  bool invariants_involved=false;
  if(spurious_check)
  {
    for(exprt::operandst::const_iterator l_it=loophead_selects.begin();
        l_it!=loophead_selects.end(); l_it++)
    {
      if(solver.get(l_it->op0()).is_true())
      {
        invariants_involved=true;
        break;
      }
    }
  }
  if(!invariants_involved || !spurious_check)
  {
    std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=goals.begin();
    for(goal_mapt::const_iterator it=goal_map.begin();
        it!=goal_map.end(); it++, g_it++)
    {
      if(property_map[it->first].result==property_checkert::resultt::UNKNOWN &&
         solver.l_get(g_it->condition).is_true())
      {
        property_map[it->first].result=property_checkert::resultt::FAIL;
        if(build_error_trace)
        {
          ssa_build_goto_tracet build_goto_trace(SSA, solver.get_solver());
          build_goto_trace(property_map[it->first].error_trace);
          if(!all_properties)
            break;
        }
      }
    }
    return;
  }

  solver.new_context();
  // force avoiding paths going through invariants

  solver << conjunction(loophead_selects);

  switch(solver())
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
  {
    std::list<cover_goals_extt::cover_goalt>::const_iterator g_it=goals.begin();
    for(goal_mapt::const_iterator it=goal_map.begin();
        it!=goal_map.end(); it++, g_it++)
    {
      if(property_map[it->first].result==property_checkert::resultt::UNKNOWN &&
         solver.l_get(g_it->condition).is_true())
      {
        property_map[it->first].result=property_checkert::resultt::FAIL;
        if(build_error_trace)
        {
          ssa_build_goto_tracet build_goto_trace(SSA, solver.get_solver());
          build_goto_trace(property_map[it->first].error_trace);

#if 0
          show_raw_countermodel(
            it->first, SSA, *solver.solver, debug(), get_message_handler());
#endif
          if(!all_properties)
            break;
        }
      }
    }
    break;
  }
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    break;

  case decision_proceduret::resultt::D_ERROR:
  default:
    throw "error from decision procedure";
  }

  solver.pop_context();

  _iterations++; // statistics
}
