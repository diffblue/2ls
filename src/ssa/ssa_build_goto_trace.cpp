/*******************************************************************\

Module: Traces of GOTO Programs for SSA Models

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Traces of GOTO Programs for SSA Models

#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/find_symbols.h>

#include "ssa_build_goto_trace.h"

exprt ssa_build_goto_tracet::finalize_lhs(const exprt &src)
{
  if(src.id()==ID_symbol)
    return src;
  else if(src.id()==ID_index)
  {
    index_exprt tmp=to_index_expr(src);
    tmp.array()=finalize_lhs(tmp.array());
    exprt index=unwindable_local_SSA.read_rhs(tmp.index(), current_pc);
    tmp.index()=simplify_expr(prop_conv.get(index), unwindable_local_SSA.ns);
    return tmp;
  }
  else if(src.id()==ID_dereference)
  {
    address_of_exprt tmp1(src);
    exprt tmp2=unwindable_local_SSA.read_rhs(tmp1, current_pc);
    exprt tmp3=prop_conv.get(tmp2);
    exprt tmp4=tmp3;
    if(tmp4.id()==ID_constant && tmp4.type().id()==ID_pointer &&
       tmp4.operands().size()==1 && tmp4.op0().id()==ID_address_of)
      tmp4=to_address_of_expr(tmp4.op0()).object();
    // TODO: investigate: produces nil sometimes
    return tmp4;
  }
  else if(src.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(src);
    tmp.struct_op()=finalize_lhs(tmp.struct_op());
    return tmp;
  }
  else
    return src;
}

bool ssa_build_goto_tracet::can_convert_ssa_expr(const exprt &expr)
{
  if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);
    return can_convert_ssa_expr(member.struct_op());
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);
    can_convert_ssa_expr(index.array());

    mp_integer idx;
    if(to_integer(to_constant_expr(index.index()), idx))
      return false;
    return true;
  }
  else if(expr.id()==ID_symbol)
  {
    return true;
  }

  return false;
}

bool ssa_build_goto_tracet::record_step(
  goto_tracet &goto_trace,
  unsigned &step_nr)
{
  bool taken=true;
  goto_trace_stept step;
  step.pc=current_pc;
  step.step_nr=step_nr;
  step.thread_nr=0;

  switch(current_pc->type)
  {
  case LOCATION:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case RETURN:
  case FUNCTION_CALL:
  case THROW:
  case CATCH:
    step.type=goto_trace_stept::typet::LOCATION;
    goto_trace.add_step(step);
    step_nr++;
    break;

  case ASSUME:
    step.type=goto_trace_stept::typet::ASSUME;
    step.cond_value=true;
    goto_trace.add_step(step);
    step_nr++;
    break;

  case GOTO:
  {
    exprt cond=current_pc->guard;
    exprt cond_read=unwindable_local_SSA.read_rhs(cond, current_pc);
    unwindable_local_SSA.rename(cond_read, current_pc);
    exprt cond_value=
      simplify_expr(prop_conv.get(cond_read), unwindable_local_SSA.ns);
    step.type=goto_trace_stept::typet::GOTO;
    step.cond_expr=cond_value; // cond
#if 0
    assert(cond_value.is_true() || cond_value.is_false());
#endif
    step.cond_value=cond_value.is_true();
#if 0
    std::cout << "COND " << from_expr(unwindable_local_SSA.ns, "", cond)
              << ": (" << from_expr(unwindable_local_SSA.ns, "", cond_read)
              << ")==" << cond_value.is_true() << std::endl;
#endif

    taken=step.cond_value;

    if(taken)
    {
      goto_trace.add_step(step);
      step_nr++;
    }
  }
  break;

  case ASSERT:
  {
    // failed or not?
    exprt cond=current_pc->guard;
    exprt cond_read=unwindable_local_SSA.read_rhs(cond, current_pc);
    unwindable_local_SSA.rename(cond_read, current_pc);
    exprt cond_value=
      simplify_expr(prop_conv.get(cond_read), unwindable_local_SSA.ns);
    if(cond_value.is_false())
    {
      step.type=goto_trace_stept::typet::ASSERT;
      step.comment=id2string(current_pc->source_location.get_comment());
      step.cond_expr=cond;
      step.cond_value=false;
      goto_trace.add_step(step);
      step_nr++;
    }
  }
  break;

  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case DECL:
  case DEAD:
    break; // ignore

  case ASSIGN:
  {
    if(has_prefix(id2string(current_pc->function), CPROVER_PREFIX))
      break;

    const code_assignt &code_assign=
      to_code_assign(current_pc->code);

    exprt rhs_ssa=unwindable_local_SSA.read_rhs(code_assign.rhs(), current_pc);
    unwindable_local_SSA.rename(rhs_ssa, current_pc);
    exprt rhs_value=prop_conv.get(rhs_ssa);
    exprt rhs_simplified=simplify_expr(rhs_value, unwindable_local_SSA.ns);
    exprt lhs_ssa=finalize_lhs(code_assign.lhs());
    exprt lhs_simplified=simplify_expr(lhs_ssa, unwindable_local_SSA.ns);

#if 0
    std::cout << "ASSIGN "
              << from_expr(unwindable_local_SSA.ns, "", code_assign)
              << ": " << from_expr(unwindable_local_SSA.ns, "", lhs_simplified)
              << " := "
              << from_expr(unwindable_local_SSA.ns, "", rhs_simplified)
              << std::endl;
#endif
    step.type=goto_trace_stept::typet::ASSIGNMENT;
    step.full_lhs=lhs_simplified;
    step.full_lhs_value=rhs_simplified;

    // filter out internal stuff
    if(lhs_simplified.id()==ID_symbol)
    {
      std::string identifier=id2string(lhs_simplified.get(ID_identifier));
      if(has_prefix(identifier, CPROVER_PREFIX))
        break;
      if(identifier.find("#")!=std::string::npos)
        break;
      if(identifier.find("$")!=std::string::npos)
        break;
      if(identifier.find("'")!=std::string::npos)
        break;
    }

    if(!can_convert_ssa_expr(lhs_simplified))
      break;

    step.lhs_object=ssa_exprt(lhs_simplified);
    step.lhs_object_value=rhs_simplified;

    // skip unresolved lhs
    if(step.lhs_object.is_nil())
      break;

    // skip strings (for SV-COMP)
    if(step.lhs_object.type().id()==ID_pointer &&
       to_pointer_type(step.lhs_object.type()).subtype().id()==ID_signedbv)
      break;

    // skip undetermined rhs
    find_symbols_sett rhs_symbols;
    find_symbols(rhs_simplified, rhs_symbols);
    if(!rhs_symbols.empty() || rhs_simplified.id()==ID_nondet_symbol)
      break;

#if 0
    std::cout << "ASSIGNMENT ADDED: "
              << from_expr(unwindable_local_SSA.ns, "", code_assign)
              << ": " << from_expr(unwindable_local_SSA.ns, "", rhs_ssa)
              << "=="
              << from_expr(unwindable_local_SSA.ns, "", step.full_lhs_value)
              << std::endl;
#endif
    goto_trace.add_step(step);
    step_nr++;
  }
  break;

  case OTHER:
    step.type=goto_trace_stept::typet::LOCATION;
    goto_trace.add_step(step);
    step_nr++;
    break;

  case NO_INSTRUCTION_TYPE:
    assert(false);
    break;
  }
  return taken;
}

/// limitation: works only for a single function
void ssa_build_goto_tracet::operator()(
  goto_tracet &goto_trace)
{
  if(unwindable_local_SSA.goto_function.body.instructions.empty())
    return;

  current_pc=unwindable_local_SSA.goto_function.body.instructions.begin();
  unwindable_local_SSA.current_unwindings.clear();
  unsigned last_level=0;
  unsigned step_nr=1;

  while(current_pc!=unwindable_local_SSA.goto_function.body.instructions.end())
  {
    unsigned current_level=
      unwindable_local_SSA.loop_hierarchy_level[current_pc].level;
    long level_diff=(long)current_level-(long)last_level;

#if 0
    std::cout << "location: " << current_pc->location_number << std::endl;
    std::cout << "current_level: " << current_level << std::endl;
    std::cout << "last_level: " << last_level << std::endl;
    std::cout << "level_diff: " << level_diff << std::endl;
#endif

    last_level=current_level;
    // we enter a loop if >0 and exit a loop if <0
    if(level_diff!=0l)
    {
      unwindable_local_SSA.decrement_unwindings(level_diff);

#if 0
      std::cout << "loop-head : " << current_pc->location_number << std::endl;
      std::cout << "unwindings: "
                << unwindable_local_SSA.odometer_to_string(
                  unwindable_local_SSA.current_unwindings,
                  100)
                << std::endl;
#endif
    }

    bool taken=record_step(goto_trace, step_nr);

    if(!goto_trace.steps.empty() &&
       goto_trace.steps.back().is_assert())
      break; // done

#if 0
    std::cout << "is_goto: " << current_pc->is_goto() << std::endl;
    std::cout << "is_backwards_goto: " << current_pc->is_backwards_goto()
              << std::endl;
    std::cout << "taken: " << taken << std::endl;
#endif

    // get successor
    if(current_pc->is_goto() && taken)
    {
      if(current_pc->is_backwards_goto())
      {
        if(unwindable_local_SSA.current_unwindings.back()==0)
          break;

        // we de-(!)-crement the unwinding counter
        unwindable_local_SSA.decrement_unwindings(0);
#if 0
        std::cout << "loop-end  : " << current_pc->location_number << std::endl;
        std::cout << "unwindings: "
                  << unwindable_local_SSA.odometer_to_string(
                    unwindable_local_SSA.current_unwindings,
                    100)
                  << std::endl;
#endif
      }
      current_pc=current_pc->get_target();
    }
    else
      current_pc++;
  }
}
