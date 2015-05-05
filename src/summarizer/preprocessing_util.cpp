#include <util/replace_expr.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <goto-instrument/unwind.h>

#include "summarizer_parse_options.h"

/*******************************************************************\

Function: summarizer_parse_optionst::inline_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parse_optionst::inline_main(goto_modelt &goto_model)
{
  goto_programt &main = goto_model.goto_functions.function_map[ID_main].body;
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

 Purpose: makeshift constant propagation to get array sizes right; 
          requires improvement, for example, there is no propagation 
                beyond the first branch target
          array sizes are updated everywhere
          casts in constants have to be evaluated, because array 
          sizes must be cast-free

\*******************************************************************/

void summarizer_parse_optionst::replace_types_rec(const replace_symbolt &replace_const, 
						 exprt &expr)
{
  replace_const(expr.type());
  for(exprt::operandst::iterator it = expr.operands().begin(); 
      it!=expr.operands().end();it++)
    replace_types_rec(replace_const,*it);
}

exprt summarizer_parse_optionst::evaluate_casts_in_constants(const exprt &expr, 
		    const typet& parent_type, bool &valid)
{
  if(expr.id()==ID_side_effect) valid = false;
  if(expr.type().id()!=ID_signedbv && expr.type().id()!=ID_unsignedbv) return expr;
  exprt r = expr;
  if(expr.id()==ID_typecast) r = evaluate_casts_in_constants(expr.op0(),expr.type(),valid);
  if(r.id()!=ID_constant) return typecast_exprt(r,parent_type);
  mp_integer v;
  to_integer(to_constant_expr(r), v);
  return from_integer(v,parent_type);
}

void summarizer_parse_optionst::propagate_constants(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    replace_symbolt replace_const;
    replace_symbolt replace_type;
    bool collect = true;
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      replace_types_rec(replace_const,i_it->guard);
      if(i_it->is_target()) collect = false; //replace constants up to first branch target
      if(i_it->is_assign())
      {
        replace_types_rec(replace_const,to_code_assign(i_it->code).rhs());
	if(collect) replace_const(to_code_assign(i_it->code).rhs());
	if(collect && to_code_assign(i_it->code).lhs().id()==ID_symbol)
	{
	  replace_symbolt::expr_mapt::iterator r_it = 
             replace_const.expr_map.find(
             to_symbol_expr(to_code_assign(i_it->code).lhs()).get_identifier());
	  if(r_it != replace_const.expr_map.end()) 
	    replace_const.expr_map.erase(r_it);
					 
	  std::set<symbol_exprt> symbols;
          find_symbols(to_code_assign(i_it->code).rhs(),symbols);
	  if(symbols.empty())
	  {
	    exprt constant = to_code_assign(i_it->code).rhs();
	    bool valid = true;
	    constant = evaluate_casts_in_constants(constant,constant.type(),
						   valid);
	    if(valid) 
  	      replace_const.insert(
                to_symbol_expr(to_code_assign(i_it->code).lhs()),
				 constant);
	  }
	}
	if(to_code_assign(i_it->code).lhs().id()==ID_index)
	{
	  replace_types_rec(replace_const,to_code_assign(i_it->code).lhs());
	}
      }
      if(i_it->is_dead()) replace_types_rec(replace_const,to_code_dead(i_it->code).symbol());
      if(i_it->is_decl())
      {
        if(collect && to_code_decl(i_it->code).symbol().type().id()==ID_array)
        {
	  replace_const(to_code_decl(i_it->code).symbol().type());
          replace_type.insert(to_symbol_expr(to_code_decl(i_it->code).symbol()).get_identifier(),
				to_code_decl(i_it->code).symbol().type());
        }
      }
//      std::cout << "code: " << i_it->code << std::endl;
    }
  }
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
	       s_it!=it->incoming_edges.end(); s_it++)
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

    for(loopst::iterator l_it = loops.begin(); l_it != loops.end(); l_it++)
    {
      std::vector<goto_programt::targett> iteration_points;
      unwind(body,l_it->second,l_it->first,k,iteration_points);
      assert(iteration_points.size()==2);
      goto_programt::targett t=body.insert_before(l_it->first);
      t->make_goto();
      t->targets.push_back(iteration_points.front());
    }
  }
}
