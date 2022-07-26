/*******************************************************************\

Module: SSA for malloc()

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA for malloc()

#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/pointer_expr.h>
#include <util/symbol.h>
#include <util/pointer_offset_size.h>

#include <analyses/constant_propagator.h>

#include <functional>

#include "malloc_ssa.h"
#include <domains/util.h>

/// Replaces the RHS of the following instruction if it is an assignemnt
/// and its LHS is equal to name. Returns whether something was changed.
bool set_following_assign_to_true(
  std::list<goto_programt::instructiont>::iterator it,
  std::list<goto_programt::instructiont>::iterator end,
  const std::string &name)
{
  bool result=false;
  for(; it!=end; it++)
  {
    if(it->is_assign())
    {
      code_assignt &code_assign=to_code_assign(it->code_nonconst());
      if(code_assign.lhs().id()==ID_symbol)
      {
        std::string lhs_id=
          id2string(to_symbol_expr(code_assign.lhs()).get_identifier());
        if(lhs_id==name)
        {
          code_assign.rhs()=true_exprt();
          result=true;
        }
      }
    }
    if(it->is_dead())
    {
      // Stop if the variable is invalid
      const code_deadt &code_dead=code_deadt{it->dead_symbol()};
      if(code_dead.symbol().id()==ID_symbol)
      {
        std::string dead_id=
          id2string(to_symbol_expr(code_dead.symbol()).get_identifier());
        if(name==dead_id)
          break;
      }
    }
    if(it->is_goto())
    {
      // Break on branching, we may not be able to set the variable in all
      // reachable branches, don't even try.
      break;
    }
  }
  return result;
}

/// Set undefined boolean variable to true. Finds declaration of a variable
/// whose name matches the given condition and adds an instruction var = TRUE
/// after the declaration.
/// \par parameters: goto_model
/// name_cond Function returning true for names of variables to be set.
void set_var_always_to_true(
  goto_modelt &goto_model,
  std::function<bool(std::string &)>name_cond)
{
  for(auto &f_it : goto_model.goto_functions.function_map)
  {
    Forall_goto_program_instructions(i_it, f_it.second.body)
    {
      if(i_it->is_decl())
      {
        const code_declt &code_decl=code_declt{i_it->decl_symbol()};
        if(code_decl.symbol().id()==ID_symbol)
        {
          std::string decl_id=
            id2string(to_symbol_expr(code_decl.symbol()).get_identifier());
          if(name_cond(decl_id))
          {
            if(set_following_assign_to_true(
              i_it,
              f_it.second.body.instructions.end(),
              decl_id))
              continue;
            // No following assignment, add one
            f_it.second.body.insert_after(
              i_it,
              goto_programt::make_assignment(
                code_assignt(code_decl.symbol(),true_exprt()),
                i_it->source_location()));
          }
        }
      }
    }
    f_it.second.body.compute_location_numbers();
    f_it.second.body.compute_target_numbers();
    f_it.second.body.compute_incoming_edges();
  }
}

void allow_record_malloc(goto_modelt &goto_model)
{
  set_var_always_to_true(
    goto_model,
    [](std::string &name)
    {
      return name.find("malloc::")!=std::string::npos &&
             name.find("::record_malloc")!=std::string::npos;
    });
}

void allow_record_memleak(goto_modelt &goto_model)
{
  set_var_always_to_true(
    goto_model,
    [](std::string &name)
    {
      return name.find("malloc::")!=std::string::npos &&
             name.find("::record_may_leak")!=std::string::npos;
    });
}

/// Removes assignments to __CPROVER_memory_leak inside free function.
/// These are in the form:
///   IF !(__CPROVER_memory_leak == free::ptr) GOTO 1
///     ASSIGN __CPROVER_memory_leak = NULL
///   1:...
void remove_free_memory_leak_assignments(
  goto_programt &goto_program,
  goto_programt::targett i_it)
{
  // Insert a skip and redirect incoming GOTOs, we will be removing the
  // instructions.
  auto skip=goto_program.insert_before(
    i_it,
    goto_programt::make_skip(i_it->source_location()));
  for(auto &target : i_it->incoming_edges)
    if(target->is_goto())
      target->set_target(skip);
  goto_program.update();

  while(i_it!=goto_program.instructions.end() &&
        i_it->is_goto() &&
        i_it->source_location().get_function()=="free")
  {
    auto next=std::next(i_it, 1);
    if (next==goto_program.instructions.end() || !next->is_assign())
      return;
    auto &symb_expr=to_symbol_expr(next->assign_lhs());
    std::string identif=symb_expr.get_identifier().c_str();
    if (identif.find("__CPROVER_memory_leak")==std::string::npos)
      return;
    // Delete the ASSIGN
    goto_program.instructions.erase(next);
    // Delete the GOTO and move forward
    goto_program.instructions.erase(i_it++);
  }
}

/// Inserts assignments to __CPROVER_memory_leak symbols into the given GOTO
/// program starting at the given location.
/// \param goto_program GOTO program to insert into.
/// \param i_it Starting location in the inlined free function.
/// \param symbols Currently defined __CPROVER_memory_leak symbols
/// \param free_ptr Symbol exprt representing the ptr being freed.
void reinsert_free_memory_leak_assignments(
  goto_programt &goto_program,
  goto_programt::targett i_it,
  const std::vector<symbolt> &symbols,
  const symbol_exprt &free_ptr)
{
  auto jump_target=i_it;
  jump_target++;
  for(const auto &symbol : symbols)
  {
    auto goto_it=goto_program.insert_after(
      i_it,
      goto_programt::make_goto(
        jump_target,
        not_exprt(
          equal_exprt(
            symbol_exprt(symbol.name, symbol.type),
            free_ptr)),
        i_it->source_location()));
    goto_program.insert_after(
      goto_it,
      goto_programt::make_assignment(
        symbol_exprt(symbol.name, symbol.type),
        null_pointer_exprt(
          to_pointer_type(symbol.type)),
        i_it->source_location()));
    jump_target=goto_it;
  }
}

/// Checks whether the expression uses __CPROVER_memory_leak symbol
bool uses_memory_leak_symbol(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const auto &symbol_expr=to_symbol_expr(expr);
    std::string identif=symbol_expr.get_identifier().c_str();
    if(identif.find("__CPROVER_memory_leak")!=std::string::npos)
      return true;
  }
  else
    for(const auto &op : expr.operands())
      if(uses_memory_leak_symbol(op))
        return true;
  return false;
}

/// Splits assignments to CPROVER_memory_leak variables to allow for
/// sound memory leak analysis of programs with multiple malloc calls
/// (e.g. after unwinding).
/// \pre malloc has been inlined.
void split_memory_leak_assignments(goto_programt &goto_program, symbol_tablet &symbol_table)
{
  symbolt leak_symbol=*symbol_table.lookup("__CPROVER_memory_leak");
  std::string base=leak_symbol.base_name.c_str();
  std::vector<symbolt> defined_symbols;
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_assign())
    {
      if(i_it->assign_lhs().id()!=ID_symbol)
        continue;
      auto &symbol_expr=to_symbol_expr(i_it->assign_lhs_nonconst());
      std::string identif=symbol_expr.get_identifier().c_str();
      if(identif.find(base)==std::string::npos)
        continue;
      if(i_it->source_location().get_function()=="malloc")
      {
        // Replace the assignment inside malloc
        symbolt new_symbol=leak_symbol;
        std::string name=base+"$"+std::to_string(i_it->location_number);
        new_symbol.name=name;
        new_symbol.base_name=name;
        symbol_table.add(new_symbol);
        symbol_expr.set_identifier(new_symbol.name);
        replace_symbol(
          i_it->assign_rhs_nonconst(),
          identif,
          new_symbol.name);
        defined_symbols.push_back(new_symbol);
      }
      else if(i_it->source_location().get_function()!="free")
      {
        // Remove initialization, we will insert it again.
        goto_program.instructions.erase(i_it++);
        i_it--;
      }
    }
    else if(i_it->is_goto() && i_it->source_location().get_function()=="free")
    {
      // Replace setting to null in free, add all the newly defined symbols
      auto next=std::next(i_it, 1);
      if(next==goto_program.instructions.end() ||
         !next->is_assign() || next->assign_lhs().id()!=ID_symbol)
        continue;
      std::string next_id=to_symbol_expr(
        next->assign_lhs()).get_identifier().c_str();
      if(next_id.find(base)==std::string::npos)
        continue;
      // The goto is in the form IF !(memory_leak = free::ptr) GOTO
      symbol_exprt ptr=to_symbol_expr(
        to_equal_expr(to_not_expr(i_it->condition()).op()).op1());
      auto prev=i_it;
      prev--;
      remove_free_memory_leak_assignments(goto_program, i_it);
      i_it=prev;
      i_it++;
      auto continue_it=i_it;
      continue_it++;
      reinsert_free_memory_leak_assignments(
        goto_program,
        i_it,
        defined_symbols,
        ptr);
      // Jump over the inserted stuff, move back one, the loop will i_it++
      i_it=continue_it;
      i_it--;
    }
    else if((i_it->is_assert() || i_it->is_assume()) &&
            uses_memory_leak_symbol(i_it->condition()))
    {
      exprt::operandst equalities;
      for(const auto &symbol : defined_symbols)
        equalities.push_back(
          equal_exprt(
            symbol_exprt(symbol.name, symbol.type),
            null_pointer_exprt(to_pointer_type(symbol.type))));
      i_it->condition_nonconst()=conjunction(equalities);
    }
  }
  // Insert new initializations
  for(const auto &symbol : defined_symbols)
    goto_program.insert_before(
      goto_program.instructions.begin(),
      goto_programt::make_assignment(
        symbol_exprt(symbol.name, symbol.type),
        null_pointer_exprt(to_pointer_type(symbol.type))));
}
