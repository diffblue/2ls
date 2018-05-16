/*******************************************************************\

Module: 2LS Command Line Options Processing

Author: Peter Schrammel

\*******************************************************************/

#include <util/replace_expr.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>

#include <analyses/constant_propagator.h>
#include <goto-instrument/unwind.h>
#include <ssa/dynobj_instance_analysis.h>

#include "2ls_parse_options.h"

/*******************************************************************\

Function: twols_parse_optionst::inline_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void twols_parse_optionst::inline_main(goto_modelt &goto_model)
{
  goto_programt &main=goto_model.goto_functions.function_map[ID__start].body;
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

bool twols_parse_optionst::unwind_goto_into_loop(
  goto_modelt &goto_model,
  unsigned k)
{
  bool result=false;
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
              result=true;
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

  return result;
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
        new_symbol.name="$deref"+i2string(var_counter++);
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

/*******************************************************************\

Function: twols_parse_optionst::remove_loops_in_entry

  Inputs:

 Outputs:

 Purpose: Remove loop head from entry instruction of a function -
          causes problems with input variables naming. If first
          instruction is target of back-jump, insert SKIP instruction
          before.

\*******************************************************************/

void twols_parse_optionst::remove_loops_in_entry(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(f_it->second.body_available() &&
       f_it->second.body.instructions.begin()->is_target())
    {
      auto new_entry=
        f_it->second.body.insert_before(f_it->second.body.instructions.begin());
      new_entry->function=f_it->first;
      new_entry->make_skip();
    }
  }
}

/*******************************************************************\

Function: twols_parse_optionst::create_dynamic_objects

  Inputs:

 Outputs:

 Purpose: Create symbols for objects pointed by parameters of a function.

\*******************************************************************/

void twols_parse_optionst::create_dynamic_objects(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assign())
      {
        code_assignt &code_assign=to_code_assign(i_it->code);
        add_dynamic_object_rec(code_assign.lhs(), goto_model.symbol_table);
        add_dynamic_object_rec(code_assign.rhs(), goto_model.symbol_table);
      }
    }
  }
}

/*******************************************************************\

Function: twols_parse_optionst::add_dynamic_object_rec

  Inputs:

 Outputs:

 Purpose: For each pointer-typed symbol in an expression which is a parameter,
          create symbol for pointed object in the symbol table.

\*******************************************************************/

void twols_parse_optionst::add_dynamic_object_rec(
  exprt &expr, symbol_tablet &symbol_table)
{
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=
      symbol_table.lookup(to_symbol_expr(expr).get_identifier());
    if(symbol.is_parameter && symbol.type.id()==ID_pointer)
    {
      // New symbol
      symbolt object_symbol;

      object_symbol.base_name=id2string(symbol.base_name)+"'obj";
      object_symbol.name=id2string(symbol.name)+"'obj";
      const typet &pointed_type=symbol.type.subtype();
      // Follow pointed type
      if(pointed_type.id()==ID_symbol)
      {
        const symbolt type_symbol=symbol_table.lookup(
          to_symbol_type(pointed_type).get_identifier());
        object_symbol.type=type_symbol.type;
      }
      else
        object_symbol.type=pointed_type;
      object_symbol.mode=ID_C;

      symbol_table.add(object_symbol);
    }
  }
  else
  {
    Forall_operands(it, expr)
      add_dynamic_object_rec(*it, symbol_table);
  }
}

/*******************************************************************\

Function: twols_parse_optionst::add_dynamic_object_symbols

  Inputs:

 Outputs:

 Purpose: Add symbols for all dynamic objects in the program into
          the symbol table.

\*******************************************************************/

void twols_parse_optionst::add_dynamic_object_symbols(
  const ssa_heap_analysist &heap_analysis,
  goto_modelt &goto_model)
{
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_function_call())
      {
        auto &fun_call=to_code_function_call(i_it->code);
        const irep_idt fname=
          to_symbol_expr(fun_call.function()).get_identifier();
        auto n_it=i_it;
        ++n_it;
        for(const symbol_exprt &o :
          heap_analysis[n_it].new_caller_objects(fname, i_it))
        {
          // New symbol
          symbolt object_symbol;

          object_symbol.name=o.get_identifier();
          object_symbol.base_name=id2string(object_symbol.name).substr(5);
          object_symbol.is_lvalue=true;

          object_symbol.type=o.type();
          object_symbol.type.set("#dynamic", true);

          object_symbol.mode=ID_C;

          goto_model.symbol_table.add(object_symbol);
        }
      }
    }
  }
}

/*******************************************************************\

Function: twols_parse_optionst::split_same_symbolic_object_assignments

  Inputs:

 Outputs:

 Purpose: Split assignments that have same symbolic dereference object
          on both sides into two separate assignments.

\*******************************************************************/

void twols_parse_optionst::split_same_symbolic_object_assignments(
  goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  unsigned counter=0;
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(i_it->is_assign())
      {
        code_assignt &assign=to_code_assign(i_it->code);
        auto lhs_sym_deref=symbolic_dereference(assign.lhs(), ns);
        if((lhs_sym_deref.id()==ID_symbol || lhs_sym_deref.id()==ID_member)
           && has_symbolic_deref(lhs_sym_deref))
        {
          while(lhs_sym_deref.id()==ID_member)
            lhs_sym_deref=to_member_expr(lhs_sym_deref).compound();

          auto rhs_sym_deref=symbolic_dereference(assign.rhs(), ns);

          std::set<symbol_exprt> rhs_symbols;
          find_symbols(rhs_sym_deref, rhs_symbols);

          if(rhs_symbols.find(to_symbol_expr(lhs_sym_deref))!=rhs_symbols.end())
          {
            symbolt tmp_symbol;
            tmp_symbol.type=assign.lhs().type();
            tmp_symbol.name="$symderef_tmp"+i2string(counter++);
            tmp_symbol.base_name=tmp_symbol.name;
            tmp_symbol.pretty_name=tmp_symbol.name;

            goto_model.symbol_table.add(tmp_symbol);

            auto new_assign=f_it->second.body.insert_after(i_it);
            new_assign->make_assignment();
            new_assign->code=code_assignt(
              assign.lhs(), tmp_symbol.symbol_expr());

            assign.lhs()=tmp_symbol.symbol_expr();
          }
        }
      }
    }
  }
}

void twols_parse_optionst::remove_dead_goto(goto_modelt &goto_model)
{
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if (i_it->is_backwards_goto())
      {
        if (i_it->guard.is_false())
          i_it->make_skip();
      }
    }
  }
}

void twols_parse_optionst::compute_dynobj_instances(
  const goto_programt &goto_program,
  const dynobj_instance_analysist &analysis,
  std::map<symbol_exprt, size_t> &instance_counts,
  const namespacet &ns)
{
  forall_goto_program_instructions(it, goto_program)
  {
    auto &analysis_value = analysis[it];
    for (auto &obj : analysis_value.live_pointers)
    {
      auto must_alias = analysis_value.dynobj_instances.find(obj.first);
      if (must_alias == analysis_value.dynobj_instances.end())
        continue;

      std::set<unsigned long> alias_classes;
      for (auto &expr : obj.second)
      {
        unsigned long n;
        must_alias->second.get_number(expr, n);
        alias_classes.insert(must_alias->second.find_number(n));
      }

      if(instance_counts.find(obj.first)==instance_counts.end() ||
         instance_counts.at(obj.first)<alias_classes.size())
      {
        instance_counts[obj.first]=alias_classes.size();
      }
    }
  }
}
