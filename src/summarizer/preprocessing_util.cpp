#include <util/replace_expr.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <goto-instrument/unwind.h>

#include "../ssa/const_propagator.h"

#include "summarizer_parse_options.h"

/*******************************************************************\

Function: summarizer_parse_optionst::inline_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parse_optionst::inline_main(goto_modelt &goto_model)
{
  goto_programt &main = goto_model.goto_functions.function_map[ID__start].body;
  goto_programt::targett target = main.instructions.begin();
  while(target!=main.instructions.end())
  {
    if(target->is_function_call())
    {
      const code_function_callt &code_function_call=
        to_code_function_call(target->code);
      irep_idt fname = code_function_call.function().get(ID_identifier); 

      debug() << "Inlining " << fname << eom;

      goto_programt tmp;
      tmp.copy_from(goto_model.goto_functions.function_map[fname].body);
      (--tmp.instructions.end())->make_skip();
      goto_model.goto_functions.function_map.erase(fname);
    
      goto_programt::targett next_target(target);
      target->make_skip();
      next_target++;
      main.instructions.splice(next_target, tmp.instructions);
      target=next_target;
    }
    else target++;
  }

  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();
}

/*******************************************************************\

Function: summarizer_parse_optionst::propagate_constants

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void summarizer_parse_optionst::propagate_constants(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    const_propagator_ait(f_it->second,ns);
  }
}

/*******************************************************************\

Function: summarizer_parse_optionst::nondet_locals

  Inputs:

 Outputs:

 Purpose: explicitly assign a nondet_symbol to local variables
          this is required by the unwinder, which would be unable
          to recognise in which scope variables have been declared

\*******************************************************************/

void summarizer_parse_optionst::nondet_locals(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_decl())
      {
	const code_declt& decl = to_code_decl(i_it->code);
        side_effect_expr_nondett nondet(decl.symbol().type());
	goto_programt::targett t = f_it->second.body.insert_after(i_it);
	t->make_assignment();
	code_assignt c(decl.symbol(),nondet);
	t->code.swap(c);
	t->source_location = i_it->source_location;
      }
    }
  }
  goto_model.goto_functions.update();
}

/*******************************************************************\

Function: goto_unwind

  Inputs:

 Outputs:

 Purpose: unwind all loops

\*******************************************************************/

void summarizer_parse_optionst::goto_unwind(goto_modelt &goto_model, unsigned k)
{
  
  typedef std::vector<std::pair<goto_programt::targett,goto_programt::targett> > loopst;

  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    goto_programt &body=f_it->second.body;
    
    loopst loops;
    Forall_goto_program_instructions(i_it, body)
    {
      if(i_it->is_backwards_goto())
      {
        goto_programt::targett loop_head = i_it->get_target();
        goto_programt::targett loop_exit = i_it;
	bool has_goto_into_loop = false;
	 
	goto_programt::targett it = loop_head;
	if(it!=loop_exit) it++;
	for(; it!=loop_exit; it++)
	{
	  for( std::set<goto_programt::targett>::iterator 
		 s_it = it->incoming_edges.begin(); 
	       s_it!=it->incoming_edges.end(); ++s_it)
	  {
	    if((*s_it)->is_goto() &&
	       (*s_it)->location_number < loop_head->location_number)
	    {
	      has_goto_into_loop = true;
	      break;
	    }
	  }
	  if(has_goto_into_loop) break;
	}
	if(has_goto_into_loop) 
	{
	  status() << "Unwinding jump into loop" << eom;
	  loops.push_back(loopst::value_type(++loop_exit,loop_head)); 
	}    
      }
    }

    for(loopst::iterator l_it = loops.begin(); l_it != loops.end(); ++l_it)
    {
      std::vector<goto_programt::targett> iteration_points;
      unwind(body,l_it->second,l_it->first,k,iteration_points);
      assert(iteration_points.size()==2);
      goto_programt::targett t=body.insert_before(l_it->first);
      t->make_goto();
      t->targets.push_back(iteration_points.front());
    }
  }
  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();
}

/*******************************************************************\

Function: remove_multiple_dereferences

  Inputs:

 Outputs:

 Purpose: temporary fix to circumvent ssa_dereference problem

\*******************************************************************/

void summarizer_parse_optionst::remove_multiple_dereferences(goto_modelt &goto_model, goto_programt &body, goto_programt::targett t, exprt &expr, unsigned &var_counter, bool deref_seen)
{
  if(expr.id()==ID_member)
  {
    member_exprt &member_expr = to_member_expr(expr);
    if(member_expr.compound().id()==ID_dereference)
    {
      dereference_exprt &deref_expr = to_dereference_expr(member_expr.compound());
      remove_multiple_dereferences(goto_model,body,t,deref_expr.pointer(),var_counter,true);
      if(deref_seen)
      {
	symbolt new_symbol;
	new_symbol.type=member_expr.type();
	new_symbol.name="$deref"+i2string(var_counter++);
	new_symbol.base_name=new_symbol.name;
	new_symbol.pretty_name=new_symbol.name;
	goto_model.symbol_table.add(new_symbol);
	goto_programt::targett t_new = body.insert_before(t);
	t_new->make_assignment();
	t_new->code = code_assignt(new_symbol.symbol_expr(),member_expr);
	expr = new_symbol.symbol_expr();
        for(std::set<goto_programt::targett>::iterator t_it = 
	      t->incoming_edges.begin();
	    t_it != t->incoming_edges.end(); ++t_it)
	{
	  (*t_it)->targets.clear();
	  (*t_it)->targets.push_back(t_new);
	}
	body.compute_location_numbers();
	body.compute_target_numbers();
	body.compute_incoming_edges();
      }
    }
    else
      Forall_operands(o_it,expr)
	remove_multiple_dereferences(goto_model,body,t,*o_it,var_counter,deref_seen);
  }
  else
    Forall_operands(o_it,expr)
      remove_multiple_dereferences(goto_model,body,t,*o_it,var_counter,deref_seen);
}

void summarizer_parse_optionst::remove_multiple_dereferences(goto_modelt &goto_model)
{
  unsigned var_counter = 0;
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_goto())
      {
	remove_multiple_dereferences(goto_model,
	  f_it->second.body,
	  i_it,
	  i_it->guard,
	  var_counter, false);
      }
      else if(i_it->is_assign())
      {
	remove_multiple_dereferences(goto_model,
	  f_it->second.body,
	  i_it,
	  to_code_assign(i_it->code).lhs(),
	  var_counter, false);
	remove_multiple_dereferences(goto_model,
	  f_it->second.body,
	  i_it,
	  to_code_assign(i_it->code).rhs(),
	  var_counter, false);
      }      
    }
  }
}
