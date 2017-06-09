/*******************************************************************\

Module: 2LS Command Line Options Processing

Author: Peter Schrammel

\*******************************************************************/

#include <util/replace_expr.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>

#include <analyses/constant_propagator.h>
#include <goto-instrument/unwind.h>

#include "2ls_parse_options.h"


/*******************************************************************\

Function: twols_parse_optionst::inline_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void twols_parse_optionst::inline_main(goto_modelt &goto_model)
{
  goto_programt &main=
    goto_model.goto_functions.function_map[goto_functionst::entry_point()].body;
  goto_programt::targett target=main.instructions.begin();
  while(target!=main.instructions.end())
  {
    if(target->is_function_call())
    {
      const code_function_callt &code_function_call=
        to_code_function_call(target->code);
      irep_idt fname=code_function_call.function().get(ID_identifier);

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
    else
      target++;
  }

  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();
}

/*******************************************************************\

Function: twols_parse_optionst::propagate_constants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void twols_parse_optionst::propagate_constants(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    constant_propagator_ait(f_it->second, ns);
  }
}

/*******************************************************************\

Function: twols_parse_optionst::nondet_locals

  Inputs:

 Outputs:

 Purpose: explicitly assign a nondet_symbol to local variables
          this is required by the unwinder, which would be unable
          to recognise in which scope variables have been declared

\*******************************************************************/

void twols_parse_optionst::nondet_locals(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_decl())
      {
        const code_declt& decl=to_code_decl(i_it->code);

        goto_programt::const_targett next=i_it; ++next;
        if(next!=f_it->second.body.instructions.end() &&
           next->is_assign() &&
           to_code_assign(next->code).lhs().id()==ID_symbol &&
           to_symbol_expr(to_code_assign(next->code).lhs())==decl.symbol())
          continue;

        side_effect_expr_nondett nondet(decl.symbol().type());
        goto_programt::targett t=f_it->second.body.insert_after(i_it);
        t->make_assignment();
        code_assignt c(decl.symbol(), nondet);
        t->code.swap(c);
        t->source_location=i_it->source_location;
      }
    }
  }
  goto_model.goto_functions.update();
}

/*******************************************************************\

Function: twols_parse_optionst::unwind_goto_into_loop

  Inputs:

 Outputs:

 Purpose: unwind all loops

\*******************************************************************/

void twols_parse_optionst::unwind_goto_into_loop(
  goto_modelt &goto_model,
  unsigned k)
{
  typedef std::vector<std::pair<goto_programt::targett,
                                goto_programt::targett> > loopst;

  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    goto_programt &body=f_it->second.body;

    loopst loops;
    Forall_goto_program_instructions(i_it, body)
    {
      if(i_it->is_backwards_goto())
      {
        goto_programt::targett loop_head=i_it->get_target();
        goto_programt::targett loop_exit=i_it;
        bool has_goto_into_loop=false;

        goto_programt::targett it=loop_head;
        if(it!=loop_exit)
          it++;
        for(; it!=loop_exit; it++)
        {
          for( std::set<goto_programt::targett>::iterator
                 s_it=it->incoming_edges.begin();
               s_it!=it->incoming_edges.end(); ++s_it)
          {
            if((*s_it)->is_goto() &&
               (*s_it)->location_number<loop_head->location_number)
            {
              has_goto_into_loop=true;
              break;
            }
          }
          if(has_goto_into_loop)
            break;
        }
        if(has_goto_into_loop)
        {
          status() << "Unwinding jump into loop" << eom;
          loops.push_back(loopst::value_type(++loop_exit, loop_head));
        }
      }
    }

    for(loopst::iterator l_it=loops.begin(); l_it!=loops.end(); ++l_it)
    {
      std::vector<goto_programt::targett> iteration_points;

      goto_unwindt goto_unwind;
      goto_unwind.unwind(
        body,
        l_it->second,
        l_it->first,
        k,
        goto_unwindt::PARTIAL, iteration_points);

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

Function: twols_parse_optionst::remove_multiple_dereferences

  Inputs:

 Outputs:

 Purpose: temporary fix to circumvent ssa_dereference problem

\*******************************************************************/

void twols_parse_optionst::remove_multiple_dereferences(
  goto_modelt &goto_model,
  goto_programt &body,
  goto_programt::targett t,
  exprt &expr,
  unsigned &var_counter,
  bool deref_seen)
{
  if(expr.id()==ID_member)
  {
    member_exprt &member_expr=to_member_expr(expr);
    if(member_expr.compound().id()==ID_dereference)
    {
      dereference_exprt &deref_expr=to_dereference_expr(member_expr.compound());
      remove_multiple_dereferences(
        goto_model, body, t, deref_expr.pointer(), var_counter, true);
      if(deref_seen)
      {
        symbolt new_symbol;
        new_symbol.type=member_expr.type();
        new_symbol.name="$deref"+std::to_string(var_counter++);
        new_symbol.base_name=new_symbol.name;
        new_symbol.pretty_name=new_symbol.name;
        goto_model.symbol_table.add(new_symbol);
        goto_programt::targett t_new=body.insert_before(t);
        t_new->make_assignment();
        t_new->code=code_assignt(new_symbol.symbol_expr(), member_expr);
        expr=new_symbol.symbol_expr();
        for(std::set<goto_programt::targett>::iterator t_it=
              t->incoming_edges.begin();
            t_it!=t->incoming_edges.end(); ++t_it)
        {
          if((*t_it)->is_goto() && (*t_it)->get_target()==t)
          {
            (*t_it)->targets.clear();
            (*t_it)->targets.push_back(t_new);
          }
        }
        body.compute_location_numbers();
        body.compute_target_numbers();
        body.compute_incoming_edges();
      }
    }
    else
      Forall_operands(o_it, expr)
        remove_multiple_dereferences(
          goto_model, body, t, *o_it, var_counter, deref_seen);
  }
  else
    Forall_operands(o_it, expr)
      remove_multiple_dereferences(
        goto_model, body, t, *o_it, var_counter, deref_seen);
}

/*******************************************************************\

Function: twols_parse_optionst::remove_multiple_dereferences

  Inputs:

 Outputs:

 Purpose: temporary fix to circumvent ssa_dereference problem

\*******************************************************************/

void twols_parse_optionst::remove_multiple_dereferences(goto_modelt &goto_model)
{
  unsigned var_counter=0;
  namespacet ns(goto_model.symbol_table);
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_goto())
      {
        remove_multiple_dereferences(
          goto_model,
          f_it->second.body,
          i_it,
          i_it->guard,
          var_counter,
          false);
      }
      else if(i_it->is_assign())
      {
        remove_multiple_dereferences(
          goto_model,
          f_it->second.body,
          i_it,
          to_code_assign(i_it->code).lhs(),
          var_counter, false);
        remove_multiple_dereferences(
          goto_model,
          f_it->second.body,
          i_it,
          to_code_assign(i_it->code).rhs(),
          var_counter, false);
      }
    }
  }
}

/*******************************************************************\

Function: twols_parse_optionst::add_assumptions_after_assertions

  Inputs:

 Outputs:

 Purpose: assumes assertions after checking them

\*******************************************************************/

void twols_parse_optionst::add_assumptions_after_assertions(
  goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assert() && !i_it->guard.is_true())
      {
        goto_programt::targett t_new=f_it->second.body.insert_after(i_it);
        t_new->make_assumption(i_it->guard);
        f_it->second.body.compute_location_numbers();
        f_it->second.body.compute_target_numbers();
        f_it->second.body.compute_incoming_edges();
      }
    }
  }
}

/*******************************************************************\

Function: twols_parse_optionst::has_threads

  Inputs:

 Outputs:

 Purpose: checks whether the program has threads

\*******************************************************************/

bool twols_parse_optionst::has_threads(const goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    const goto_programt& program=f_it->second.body;

    forall_goto_program_instructions(i_it, program)
    {
      const goto_programt::instructiont &instruction=*i_it;

      if(instruction.is_function_call())
      {
        const code_function_callt &fct=to_code_function_call(instruction.code);
        if(fct.function().id()==ID_symbol)
        {
          const symbol_exprt &fsym=to_symbol_expr(fct.function());

          if(ns.lookup(fsym.get_identifier()).base_name=="pthread_create")
            return true;
        }
      }
    }
  }
  return false;
}

/*******************************************************************\

Function: twols_parse_optionst::filter_assertions

  Inputs:

 Outputs:

 Purpose: filter certain assertions for SV-COMP

\*******************************************************************/

void twols_parse_optionst::filter_assertions(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    goto_programt &program=f_it->second.body;

    Forall_goto_program_instructions(i_it, program)
    {
      if(!i_it->is_assert())
        continue;

      if(i_it->source_location.get_comment()=="free argument is dynamic object")
        i_it->make_skip();
    }
  }
}

/*******************************************************************\

Function: twols_parse_optionst::split_loopheads

Inputs:

Outputs:

Purpose: insert skip at jump targets if they are goto,
         assume or assert instructions

\*******************************************************************/

void twols_parse_optionst::split_loopheads(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_backwards_goto())
        continue;
      goto_programt::targett loophead=i_it->get_target();
      if(i_it->guard.is_true() && !loophead->is_assert())
        continue;

      // inserts the skip
      goto_programt::targett new_loophead=
        f_it->second.body.insert_before(loophead);
      new_loophead->make_skip();
      new_loophead->source_location=loophead->source_location;
      new_loophead->function=i_it->function;

      // update jumps to loophead
      for(std::set<goto_programt::targett>::iterator j_it=
            loophead->incoming_edges.begin();
          j_it!=loophead->incoming_edges.end(); j_it++)
      {
        if(!(*j_it)->is_goto() || (*j_it)->get_target()!=loophead)
          continue;
        (*j_it)->targets.clear();
        (*j_it)->targets.push_back(new_loophead);
      }
    }
  }
}
