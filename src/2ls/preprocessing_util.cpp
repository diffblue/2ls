/*******************************************************************\

Module: 2LS Command Line Options Processing

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// 2LS Command Line Options Processing

#include <util/replace_expr.h>
#include <util/pointer_expr.h>
#include <util/find_symbols.h>
#include <util/arith_tools.h>
#include <util/std_code.h>

#include <analyses/constant_propagator.h>
#include <goto-instrument/unwind.h>
#include <goto-instrument/function.h>
#include <ssa/dynobj_instance_analysis.h>

#include "2ls_parse_options.h"

void twols_parse_optionst::inline_main(goto_modelt &goto_model)
{
  irep_idt start=goto_functionst::entry_point();
  goto_programt &main=goto_model.goto_functions.function_map[start].body;
  goto_programt::targett target=main.instructions.begin();
  while(target!=main.instructions.end())
  {
    if(target->is_function_call())
    {
      irep_idt fname=target->call_function().get(ID_identifier);

      debug() << "Inlining " << fname << eom;

      goto_programt tmp;
      tmp.copy_from(goto_model.goto_functions.function_map[fname].body);
      (--tmp.instructions.end())->turn_into_skip();
      goto_model.goto_functions.function_map.erase(fname);

      goto_programt::targett next_target(target);
      target->turn_into_skip();
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

void twols_parse_optionst::propagate_constants(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    constant_propagator_ait const_propagator(f_it.second);
    const_propagator(f_it.first, f_it.second, ns);
  }
}

/// explicitly assign a nondet_symbol to local variables this is required by the
/// unwinder, which would be unable to recognise in which scope variables have
/// been declared
void twols_parse_optionst::nondet_locals(goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_decl())
      {
        const code_declt& decl=code_declt{i_it->decl_symbol()};

        goto_programt::const_targett next=i_it; ++next;
        if(next!=f_it.second.body.instructions.end() &&
           next->is_assign() &&
           next->assign_lhs().id()==ID_symbol &&
           to_symbol_expr(next->assign_lhs())==decl.symbol())
          continue;

        side_effect_expr_nondett nondet(
          decl.symbol().type(),
          i_it->source_location());
        f_it.second.body.insert_after(
          i_it,
          goto_programt::make_assignment(
            code_assignt(decl.symbol(), nondet),
            i_it->source_location()));
      }
    }
  }
  goto_model.goto_functions.update();
}

/// unwind all loops
bool twols_parse_optionst::unwind_goto_into_loop(
  goto_modelt &goto_model,
  unsigned k)
{
  bool result=false;
  typedef std::vector<std::pair<goto_programt::targett,
                                goto_programt::targett> > loopst;

  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    goto_programt &body=f_it.second.body;

    loopst loops;
    Forall_goto_program_instructions(i_it, body)
    {
      bool is_loop_head=false;
      goto_programt::targett loop_exit;
      for(auto edge : i_it->incoming_edges)
      {
        if(edge->location_number>i_it->location_number)
        {
          is_loop_head=true;
          loop_exit=edge;
        }
      }

      if(is_loop_head)
      {
        bool has_goto_into_loop=false;

        goto_programt::targett it=i_it;
        if(it!=loop_exit)
          it++;
        for(; it!=loop_exit; it++)
        {
          for( std::set<goto_programt::targett>::iterator
                 s_it=it->incoming_edges.begin();
               s_it!=it->incoming_edges.end(); ++s_it)
          {
            if((*s_it)->is_goto() &&
               (*s_it)->location_number<i_it->location_number)
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
          loops.push_back(loopst::value_type(++loop_exit, i_it));
        }
      }
    }

    for(loopst::iterator l_it=loops.begin(); l_it!=loops.end(); ++l_it)
    {
      std::vector<goto_programt::targett> iteration_points;

      goto_unwindt goto_unwind;
      goto_unwind.unwind(
        f_it.first,
        body,
        l_it->second,
        l_it->first,
        k,
        goto_unwindt::unwind_strategyt::PARTIAL, iteration_points);

      assert(iteration_points.size()==2);
      body.insert_before(
        l_it->first,
        goto_programt::make_goto(
          iteration_points.front(),
          l_it->first->source_location()));
    }
  }
  goto_model.goto_functions.update();
  goto_model.goto_functions.compute_loop_numbers();

  return result;
}

/// temporary fix to circumvent ssa_dereference problem
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
        goto_programt::targett t_new=body.insert_before(
          t,
          goto_programt::make_assignment(
            code_assignt(new_symbol.symbol_expr(), member_expr),
            t->source_location()));
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

/// temporary fix to circumvent ssa_dereference problem
void twols_parse_optionst::remove_multiple_dereferences(goto_modelt &goto_model)
{
  unsigned var_counter=0;
  namespacet ns(goto_model.symbol_table);
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_goto() || i_it->is_assert())
      {
        remove_multiple_dereferences(
          goto_model,
          f_it.second.body,
          i_it,
          i_it->condition_nonconst(),
          var_counter,
          false);
      }
      else if(i_it->is_assign())
      {
        remove_multiple_dereferences(
          goto_model,
          f_it.second.body,
          i_it,
          to_code_assign(i_it->code_nonconst()).lhs(),
          var_counter, false);
        remove_multiple_dereferences(
          goto_model,
          f_it.second.body,
          i_it,
          to_code_assign(i_it->code_nonconst()).rhs(),
          var_counter, false);
      }
    }
  }
}

/// assumes assertions after checking them
void twols_parse_optionst::add_assumptions_after_assertions(
  goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_assert() && !i_it->condition().is_true())
      {
        f_it.second.body.insert_after(
          i_it,
          goto_programt::make_assumption(
            i_it->condition(),
            i_it->source_location()));
        f_it.second.body.compute_location_numbers();
        f_it.second.body.compute_target_numbers();
        f_it.second.body.compute_incoming_edges();
      }
    }
  }
}

/// checks whether the program has threads
bool twols_parse_optionst::has_threads(const goto_modelt &goto_model)
{
  namespacet ns(goto_model.symbol_table);
  for(const auto &f_it : goto_model.goto_functions.function_map)
  {
    const goto_programt& program=f_it.second.body;

    forall_goto_program_instructions(i_it, program)
    {
      const goto_programt::instructiont &instruction=*i_it;

      if(instruction.is_function_call())
      {
        if(instruction.call_function().id()==ID_symbol)
        {
          const symbol_exprt &fsym=to_symbol_expr(instruction.call_function());

          if(ns.lookup(fsym.get_identifier()).base_name=="pthread_create")
            return true;
        }
      }
    }
  }
  return false;
}

/// filter certain assertions for SV-COMP
void twols_parse_optionst::filter_assertions(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    goto_programt &program=f_it.second.body;

    Forall_goto_program_instructions(i_it, program)
    {
      if(!i_it->is_assert())
        continue;

      if(i_it->source_location().get_comment()==
          "free argument is dynamic object")
        i_it->turn_into_skip();
    }
  }
}

/// insert skip at jump targets if they are goto, assume or assert instructions
void twols_parse_optionst::split_loopheads(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(!i_it->is_backwards_goto())
        continue;
      goto_programt::targett loophead=i_it->get_target();
      if(i_it->condition().is_true() && !loophead->is_assert())
        continue;

      // inserts the skip
      goto_programt::targett new_loophead=
        f_it.second.body.insert_before(
          loophead,
          goto_programt::make_skip(loophead->source_location()));

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

/// Remove loop head from entry instruction of a function - causes problems with
/// input variables naming. If first instruction is target of back-jump, insert
/// SKIP instruction before.
void twols_parse_optionst::remove_loops_in_entry(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    if(f_it.second.body_available() &&
       f_it.second.body.instructions.begin()->is_target())
    {
      auto insert_before=f_it.second.body.instructions.begin();
      f_it.second.body.insert_before(
        insert_before,
        goto_programt::make_skip(insert_before->source_location()));
    }
  }
}

/// Create symbols for objects pointed by parameters of a function.
void twols_parse_optionst::create_dynamic_objects(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_assign())
      {
        code_assignt &code_assign=to_code_assign(i_it->code_nonconst());
        add_dynamic_object_rec(code_assign.lhs(), goto_model.symbol_table);
        add_dynamic_object_rec(code_assign.rhs(), goto_model.symbol_table);
      }
    }
  }
}

/// For each pointer-typed symbol in an expression which is a parameter, create
/// symbol for pointed object in the symbol table.
void twols_parse_optionst::add_dynamic_object_rec(
  exprt &expr, symbol_tablet &symbol_table)
{
  if(expr.id()==ID_symbol)
  {
    const symbolt &symbol=
      symbol_table.lookup_ref(to_symbol_expr(expr).get_identifier());
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
        const symbolt type_symbol=symbol_table.lookup_ref(
          to_struct_tag_type(pointed_type).get_identifier());
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

/// Split assignments that have same symbolic dereference object on both sides
/// into two separate assignments.
void twols_parse_optionst::split_same_symbolic_object_assignments(
  goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);
  unsigned counter=0;
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_assign())
      {
        code_assignt &assign=to_code_assign(i_it->code_nonconst());
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
            tmp_symbol.name="$symderef_tmp"+std::to_string(counter++);
            tmp_symbol.base_name=tmp_symbol.name;
            tmp_symbol.pretty_name=tmp_symbol.name;

            goto_model.symbol_table.add(tmp_symbol);

            f_it.second.body.insert_after(
              i_it,
              goto_programt::make_assignment(
                code_assignt(assign.lhs(), tmp_symbol.symbol_expr()),
                i_it->source_location()));
            assign.lhs()=tmp_symbol.symbol_expr();
          }
        }
      }
    }
  }
}

/// Remove dead backwards GOTO instructions (having false as guard)
void twols_parse_optionst::remove_dead_goto(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_backwards_goto())
      {
        if(i_it->condition().is_false())
          i_it->turn_into_skip();
      }
    }
  }
}

void twols_parse_optionst::memory_assert_info(goto_modelt &goto_model)
{
  irep_idt file;
  irep_idt line;

  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(!i_it->source_location().get_file().empty())
      {
        file=i_it->source_location().get_file();
      }
      if(!i_it->source_location().get_line().empty())
      {
        line=i_it->source_location().get_line();
      }

      if(i_it->is_assert())
      {
        const auto &guard=i_it->condition();
        if(guard.id()==ID_equal)
        {
          const equal_exprt &equal=to_equal_expr(guard);
          if(equal.op0().id()==ID_symbol)
          {
            const auto &id=id2string(
              to_symbol_expr(equal.op0()).get_identifier());
            if(id.find("__CPROVER_memory_leak")!=std::string::npos)
            {
              if(!file.empty())
                i_it->source_location_nonconst().set_file(file);
              if(!line.empty())
                i_it->source_location_nonconst().set_line(line);
            }
          }
        }
      }
    }
  }
}

/// Transform comparison of pointers to be non-deterministic if the pointers
/// were freed.
/// This is done by transforming (x op y) into:
///     (x op y) XOR ((freed(x) || nondet) && (freed(y) && nondet))
void make_freed_ptr_comparison_nondet(
  goto_modelt &goto_model,
  goto_functionst::goto_functiont &fun,
  goto_programt::instructionst::iterator loc,
  exprt &cond,
  const std::set<irep_idt> &typecasted_pointers)
{
  if(cond.id()==ID_equal || cond.id()==ID_notequal || cond.id()==ID_le ||
     cond.id()==ID_lt || cond.id()==ID_ge || cond.id()==ID_gt)
  {
    binary_exprt &bin=to_binary_expr(cond);
    // Check if both operands are either pointers or type-casted pointers
    if(bin.op0().id() == ID_symbol && bin.op1().id() == ID_symbol &&
       !is_cprover_symbol(bin.op0()) && !is_cprover_symbol(bin.op1()) &&
       (bin.op0().type().id() == ID_pointer ||
        typecasted_pointers.find(to_symbol_expr(bin.op0()).get_identifier()) !=
        typecasted_pointers.end()) &&
       (bin.op1().type().id() == ID_pointer ||
        typecasted_pointers.find(to_symbol_expr(bin.op1()).get_identifier()) !=
        typecasted_pointers.end()))
    {
      const symbolt &freed=goto_model.symbol_table.lookup_ref(
        "__CPROVER_deallocated");

      // LHS != __CPROVER_deallocated
      auto lhs_not_freed_cond=notequal_exprt(
        typecast_exprt(bin.op0(), freed.type), freed.symbol_expr());

      // RHS != __CPROVER_deallocated
      auto rhs_not_freed_cond=notequal_exprt(
        typecast_exprt(bin.op1(), freed.type), freed.symbol_expr());

      // XOR is implemented as ==
      cond=equal_exprt(
        cond,
        and_exprt(
          or_exprt(
            lhs_not_freed_cond,
            side_effect_expr_nondett(bool_typet(), loc->source_location())),
          or_exprt(
            rhs_not_freed_cond,
            side_effect_expr_nondett(bool_typet(), loc->source_location()))));
    }
  }
  else if(cond.id()==ID_not)
    make_freed_ptr_comparison_nondet(
      goto_model, fun, loc, to_not_expr(cond).op(), typecasted_pointers);
}

/// Transform each comparison of pointers so that it has a non-deterministic
/// result if the pointers were freed, since comparison of freed pointers is
/// an undefined behavior.
void twols_parse_optionst::handle_freed_ptr_compare(goto_modelt &goto_model)
{
  std::set<irep_idt> typecasted_pointers;
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_goto() || i_it->is_assert())
      {
        auto &guard=i_it->condition_nonconst();
        make_freed_ptr_comparison_nondet(
          goto_model, f_it.second, i_it, guard, typecasted_pointers);
      }
      else if(i_it->is_assign())
      {
        const exprt &assign_lhs=i_it->assign_lhs();
        const exprt &assign_rhs=i_it->assign_rhs();
        // If a pointer is casted to a non-pointer type (probably an integer),
        // save the destination variable into typecasted_pointers
        if(assign_lhs.id()==ID_symbol &&
           ((assign_rhs.id()==ID_typecast &&
             to_typecast_expr(assign_rhs).op().type().id()==ID_pointer &&
             assign_lhs.type().id()!=ID_pointer) ||
            typecasted_pointers.find(
              to_symbol_expr(assign_lhs).get_identifier())!=
            typecasted_pointers.end()))
        {
          typecasted_pointers.insert(
            to_symbol_expr(assign_lhs).get_identifier());
        }
      }
    }
  }
}

/// Fail if the program contains any functions that 2LS does not currently
/// support. These include:
///     - builtin gcc functions
///     - longjmp (not supported by CBMC)
void twols_parse_optionst::assert_no_unsupported_functions(
  goto_modelt &goto_model)
{
  forall_goto_program_instructions(
    i_it,
    goto_model.goto_functions.function_map.find(
      goto_model.goto_functions.entry_point())->second.body)
  {
    std::string name=id2string(i_it->source_location().get_function());
    assert(
      name.find("__builtin_")==std::string::npos &&
      name.find("__CPROVER_overflow")==std::string::npos);
    assert(name != "longjmp" && name != "_longjmp" && name != "siglongjmp");

    if(i_it->is_assign())
    {
      assert(i_it->code().op1().id()!=ID_popcount);
    }
  }
}

/// Prevents usage of atexit function which is not supported, yet
/// Must be called before inlining since it will lose the calls
void twols_parse_optionst::assert_no_atexit(goto_modelt &goto_model)
{
  for(const auto &f_it : goto_model.goto_functions.function_map)
  {
    forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_function_call())
      {
        const auto &function=i_it->call_function();
        if(!(function.id()==ID_symbol))
          continue;
        auto &name=id2string(to_symbol_expr(function).get_identifier());
        assert(name!="atexit");
      }
    }
  }
}

/// Searches for SKIP instructions that are a target of both a forward and
/// a backward GOTO. Such instructions are split into 2 - the first one is
/// made the target of forward GOTOs and the second one is made the target of
/// backward GOTOs.
void twols_parse_optionst::fix_goto_targets(goto_modelt &goto_model)
{
  for (auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if (i_it->incoming_edges.size() <= 1)
        continue;
      if (!i_it->is_skip())
        continue;

      bool has_backwards_goto = false;
      bool has_forward_goto = false;
      for (auto &incoming : i_it->incoming_edges)
      {
        if (incoming->location_number < i_it->location_number)
          has_forward_goto = true;
        if (incoming->location_number > i_it->location_number)
          has_backwards_goto = true;
      }
      if (has_forward_goto && has_backwards_goto)
      {
        auto new_skip = f_it.second.body.insert_after(
          i_it,
          goto_programt::make_skip(i_it->source_location()));

        for (auto &incoming : i_it->incoming_edges)
        {
          if (incoming->location_number > i_it->location_number)
          {
            // Redirect backward GOTOs to the new skip
            for (auto &target : incoming->targets)
            {
              if (target == i_it)
                target = new_skip;
            }
          }
        }
      }
    }
    goto_model.goto_functions.update();
  }
}


/// Converts assertion conditions into false.
void twols_parse_optionst::make_assertions_false(goto_modelt &goto_model)
{
  for(auto &f : goto_model.goto_functions.function_map)
    for(auto &i : f.second.body.instructions)
      if(i.is_assert())
        i.condition_nonconst()=false_exprt();
}

void set_array_size_rec(const exprt &old_size,
                        const exprt &new_size,
                        exprt &expr)
{
  if(expr.type().id() == ID_array)
  {
    auto &array_type = to_array_type(expr.type());
    if(array_type.size() == old_size)
      array_type.size() = new_size;
  }
  else
  {
    Forall_operands(o_it, expr)
      set_array_size_rec(old_size, new_size, *o_it);
  }
}

/// Find all arrays that have the size equal to old_size and replace their size
/// by new_size.
void set_array_size(goto_programt &goto_function,
                    const exprt &old_size,
                    const exprt &new_size)
{
  Forall_goto_program_instructions(it, goto_function)
  {
    if(it->has_condition())
      set_array_size_rec(old_size, new_size, it->condition_nonconst());

    if(it->is_decl())
      set_array_size_rec(old_size, new_size, it->decl_symbol());
    else if(it->is_assign())
    {
      if(it->assign_lhs() != new_size)
      {
        set_array_size_rec(old_size, new_size, it->assign_lhs_nonconst());
        set_array_size_rec(old_size, new_size, it->assign_rhs_nonconst());
      }
    }
  }
}

/// Transform array declarations of the form:
///   DECL <array> : <type>[<const>]
/// into:
///   $array_size#i = <const>
///   DECL <array> : <type>[$array_size#i]
/// This way, the solver will handle the array quickly, even if the size is huge
void twols_parse_optionst::make_symbolic_array_indices(goto_modelt &goto_model)
{
  int i = 0;
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_decl())
      {
        auto &symbol = i_it->decl_symbol();
        if(symbol.type().id() == ID_array)
        {
          auto &array_type = to_array_type(symbol.type());

          if(!array_type.size().is_constant())
            continue;

          auto next = i_it;
          next++;
          if(next->is_assign() && next->assign_lhs() == symbol)
            continue;

          // New symbol $array_size
          symbolt size;
          size.type = array_type.size().type();
          size.name = "$array_size" + std::to_string(i++);
          size.base_name = size.name;
          size.pretty_name = size.name;
          goto_model.symbol_table.add(size);

          // Declare $array_size
          auto size_decl = goto_programt::make_decl(
            code_declt(size.symbol_expr()), i_it->source_location());
          f_it.second.body.insert_before(i_it, size_decl);

          // $array_size = original size
          auto size_assign = goto_programt::make_assignment(
            code_assignt(size.symbol_expr(), array_type.size()),
            i_it->source_location());
          f_it.second.body.insert_before(i_it, size_assign);

          // Propagate the new size into all usages of the array
          exprt old_size = array_type.size(); // copy as it will change
          set_array_size(f_it.second.body, old_size, size.symbol_expr());
        }
      }
    }
  }
  goto_model.goto_functions.update();
}

/// Makes user input nondeterministic, i.e. arguments of fscanf starting
/// from the second one are assigned a nondeterministic value.
void twols_parse_optionst::make_scanf_nondet(goto_modelt &goto_model)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(!i_it->is_function_call())
        continue;
      auto name = to_symbol_expr(i_it->call_function()).get_identifier();
      // FIXME: this is a bit hacky and should probably be handled better in
      //        coordination with CBMC.
      int start;
      if(name == "__isoc99_fscanf" || name == "fscanf")
        start = 2;
      else if(name == "__isoc99_scanf" || name == "scanf")
        start = 1;
      else
        continue;
      int i = 0;
      for(const auto &arg : i_it->call_arguments())
      {
        if(i >= start)
        {
          if(arg.id() == ID_address_of)
          {
            auto lhs = dereference_exprt(arg);
            side_effect_expr_nondett rhs(
              to_address_of_expr(arg).object().type(), i_it->source_location());
            f_it.second.body.insert_after(
              i_it, goto_programt::make_assignment(lhs, rhs));
          }
        }
        i++;
      }
    }
  }
}
