/*******************************************************************\

Module: Traces of GOTO Programs for SSA Models

Author: Daniel Kroening

Date: June 2014

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "ssa_build_goto_trace.h"

/*******************************************************************\

Function: finalize_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt finalize_lhs(
  const exprt &src,
  const local_SSAt &local_SSA,
  const prop_convt &prop_conv,
  goto_programt::const_targett current_pc)
{
  if(src.id()==ID_symbol)
    return src;
  else if(src.id()==ID_index)
  {
    index_exprt tmp=to_index_expr(src);
    tmp.array()=finalize_lhs(tmp.array(), local_SSA, prop_conv, current_pc);
    tmp.index()=simplify_expr(prop_conv.get(local_SSA.read_rhs(tmp.index(), current_pc)), local_SSA.ns);
    return tmp;
  }
  else if(src.id()==ID_dereference)
  {
    address_of_exprt tmp1(src);
    exprt tmp2=local_SSA.read_rhs(tmp1, current_pc);
    exprt tmp3=prop_conv.get(tmp2);
    exprt tmp4=tmp3;
    if(tmp4.id()==ID_constant && tmp4.type().id()==ID_pointer &&
       tmp4.operands().size()==1 && tmp4.op0().id()==ID_address_of)
      tmp4=to_address_of_expr(tmp4.op0()).object();
    return tmp4;
  }
  else if(src.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(src);
    tmp.struct_op()=finalize_lhs(tmp.struct_op(), local_SSA, prop_conv, current_pc);
    return tmp;
  }
  else
    return src;
}

/*******************************************************************\

Function: record_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void record_step(
  const local_SSAt &local_SSA,
  const prop_convt &prop_conv,
  goto_programt::const_targett current_pc,
  goto_tracet &goto_trace,
  unsigned &step_nr)
{
  goto_trace_stept step;
  step.pc=current_pc;
  step.step_nr=step_nr;
  step.thread_nr=0;

  switch(current_pc->type)
  {
  case GOTO:
  case LOCATION:
  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case RETURN:
  case FUNCTION_CALL:
  case THROW:
  case CATCH:
    step.type=goto_trace_stept::LOCATION;
    goto_trace.add_step(step);
    break;

  case ASSUME:
    step.type=goto_trace_stept::ASSUME;
    step.cond_value=true;
    goto_trace.add_step(step);
    break;
  
  case ASSERT:
    {
      // failed or not?
      exprt cond=current_pc->guard;
      exprt cond_read=local_SSA.read_rhs(cond, current_pc);
      exprt cond_value=simplify_expr(prop_conv.get(cond_read), local_SSA.ns);
      if(cond_value.is_false())
      {
        step.type=goto_trace_stept::ASSERT;
        step.comment=id2string(current_pc->location.get_comment());
        step.cond_expr=cond;
        step.cond_value=false;
        goto_trace.add_step(step);
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
      const code_assignt &code_assign=
        to_code_assign(current_pc->code);
      exprt rhs_ssa=local_SSA.read_rhs(code_assign.rhs(), current_pc);
      exprt rhs_value=prop_conv.get(rhs_ssa);
      exprt rhs_simplified=simplify_expr(rhs_value, local_SSA.ns);
      exprt lhs_ssa=finalize_lhs(code_assign.lhs(), local_SSA, prop_conv, current_pc);
      exprt lhs_simplified=simplify_expr(lhs_ssa, local_SSA.ns);

      step.type=goto_trace_stept::ASSIGNMENT;
      // step.lhs_object
      // step.lhs_object_value
      step.full_lhs=lhs_simplified;
      step.full_lhs_value=rhs_simplified;
      goto_trace.add_step(step);
      step_nr++;
    }
    break;

  case OTHER:
    step.type=goto_trace_stept::LOCATION;
    goto_trace.add_step(step);
    break;
    
  case NO_INSTRUCTION_TYPE:
    assert(false);
    break;
  }
}

/*******************************************************************\

Function: build_goto_trace

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build_goto_trace(
  const local_SSAt &local_SSA,
  const prop_convt &prop_conv,
  goto_tracet &goto_trace)
{
  if(local_SSA.goto_function.body.instructions.empty())
    return;
  
  goto_programt::const_targett current_pc;

  current_pc=local_SSA.goto_function.body.instructions.begin();
  
  unsigned step_nr=1;
  
  while(current_pc!=local_SSA.goto_function.body.instructions.end())
  {
    record_step(local_SSA, prop_conv, current_pc, goto_trace, step_nr);
    
    if(!goto_trace.steps.empty() &&
       goto_trace.steps.back().is_assert())
      break; // done
    
    // get successor
    if(current_pc->is_goto())
    {
      // taken or not?
      exprt cond_symbol=local_SSA.cond_symbol(current_pc);
      exprt cond_value=prop_conv.get(cond_symbol);

      if(cond_value.is_true())
      {
        if(current_pc->is_backwards_goto())
          current_pc++;
        else
          current_pc=current_pc->get_target();
      }
      else
        current_pc++;
    }
    else
      current_pc++;
  }
}
