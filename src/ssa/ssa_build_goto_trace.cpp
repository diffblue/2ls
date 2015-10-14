/*******************************************************************\

Module: Traces of GOTO Programs for SSA Models

Author: Daniel Kroening

\*******************************************************************/

#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "ssa_build_goto_trace.h"

/*******************************************************************\

Function: ssa_build_goto_tracet::finalize_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt ssa_build_goto_tracet::finalize_lhs(const exprt &src)
{
  if(src.id()==ID_symbol)
    return src;
  else if(src.id()==ID_index)
  {
    index_exprt tmp=to_index_expr(src);
    tmp.array()=finalize_lhs(tmp.array());
    exprt index = ssa_local_unwinder2.read_rhs(tmp.index(),current_pc);
    tmp.index()=simplify_expr(prop_conv.get(index), ssa_local_unwinder2.ns);
    return tmp;
  }
  else if(src.id()==ID_dereference)
  {
    address_of_exprt tmp1(src);
    exprt tmp2 = ssa_local_unwinder2.read_rhs(tmp1,current_pc);
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
    tmp.struct_op()=finalize_lhs(tmp.struct_op());
    return tmp;
  }
  else
    return src;
}

/*******************************************************************\

Function: ssa_build_goto_tracet::record_step

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ssa_build_goto_tracet::record_step(
  goto_tracet &goto_trace,
  unsigned &step_nr)
{
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
    step.type=goto_trace_stept::LOCATION;
    goto_trace.add_step(step);
    step_nr++;
    break;

  case ASSUME:
    step.type=goto_trace_stept::ASSUME;
    step.cond_value=true;
    goto_trace.add_step(step);
    step_nr++;
    break;
  
  case GOTO:
    {
      exprt cond=current_pc->guard;
      exprt cond_read = ssa_local_unwinder2.read_rhs(cond,current_pc);
      exprt cond_value=simplify_expr(prop_conv.get(cond_read), ssa_local_unwinder2.ns);
      step.type=goto_trace_stept::GOTO;
      step.cond_expr = cond;
      step.cond_value = cond_value.is_true();
      goto_trace.add_step(step);
      step_nr++;
    }
    break;

  case ASSERT:
    {
      // failed or not?
      exprt cond=current_pc->guard;
      exprt cond_read=ssa_local_unwinder2.read_rhs(cond,current_pc);
      exprt cond_value=simplify_expr(prop_conv.get(cond_read), ssa_local_unwinder2.ns);
      if(cond_value.is_false())
      {
        step.type=goto_trace_stept::ASSERT;
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
      const code_assignt &code_assign=
        to_code_assign(current_pc->code);
      exprt rhs_ssa=ssa_local_unwinder2.read_rhs(code_assign.rhs(),current_pc);
      exprt rhs_value=prop_conv.get(rhs_ssa);
      exprt rhs_simplified=simplify_expr(rhs_value, ssa_local_unwinder2.ns);
      exprt lhs_ssa=finalize_lhs(code_assign.lhs());
      exprt lhs_simplified=simplify_expr(lhs_ssa, ssa_local_unwinder2.ns);

      step.type=goto_trace_stept::ASSIGNMENT;
      step.full_lhs=lhs_simplified;
      step.full_lhs_value=rhs_simplified;
      if(lhs_simplified.id()==ID_symbol) 
      {
	step.lhs_object = to_symbol_expr(lhs_simplified);
        step.lhs_object_value=rhs_simplified;
      }      
      goto_trace.add_step(step);
      step_nr++;
    }
    break;

  case OTHER:
    step.type=goto_trace_stept::LOCATION;
    goto_trace.add_step(step);
    step_nr++;
    break;
    
  case NO_INSTRUCTION_TYPE:
    assert(false);
    break;
  }
}

/*******************************************************************\

Function: ssa_build_goto_tracet::operator()

  Inputs:

 Outputs:

 Purpose: limitation: works only for a single function

\*******************************************************************/

void ssa_build_goto_tracet::operator()(
  goto_tracet &goto_trace)
{
  if(ssa_local_unwinder2.goto_function.body.instructions.empty())
    return;

  current_pc=ssa_local_unwinder2.goto_function.body.instructions.begin();
  ssa_local_unwinder2.current_unwindings.clear();  
  unsigned last_level = 0;
  unsigned step_nr=1;
  
  while(current_pc!=ssa_local_unwinder2.goto_function.body.instructions.end())
  {
#if 0
    if(current_pc->is_assign())
    {
      const code_assignt &code_assign = to_code_assign(current_pc->code);
      if(code_assign.rhs().id()==ID_side_effect &&
	 to_side_effect_expr(code_assign.rhs()).get_statement()==ID_nondet)
      {
	current_pc++;
	continue;
      }
    }
#endif
    unsigned current_level = 
      ssa_local_unwinder2.loop_hierarchy_level[current_pc];
    int level_diff = current_level - last_level;
    last_level = current_level;
    if(level_diff!=0)
      ssa_local_unwinder2.decrement_unwindings(level_diff);
#if 1
    std::cout << "location: " << current_pc->location_number << std::endl;
    std::cout << "level_diff: " << level_diff << std::endl;
    std::cout << "unwindings: " 
	      << ssa_local_unwinder2.odometer_to_string(ssa_local_unwinder2.current_unwindings,100) << std::endl;
#endif

    record_step(goto_trace, step_nr);
    
    if(!goto_trace.steps.empty() &&
       goto_trace.steps.back().is_assert())
      break; // done
    
    // get successor
    if(current_pc->is_goto())
    {
      // taken or not?
      symbol_exprt cond_symbol=ssa_local_unwinder2.cond_symbol(current_pc);
      exprt cond_value=prop_conv.get(cond_symbol);
#if 1
      std::cout << "COND: " << cond_symbol.get_identifier() 
		<< " == " << cond_value.is_true() << std::endl;
#endif
      if(cond_value.is_true())
      {
        if(current_pc->is_backwards_goto())
	{
          ssa_local_unwinder2.decrement_unwindings(0);
	}
        current_pc=current_pc->get_target();
      }
      else
        current_pc++;
    }
    else
      current_pc++;
  }
}
