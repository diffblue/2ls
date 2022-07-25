/*******************************************************************\

Module: A map of program locations to the assignments made there

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A map of program locations to the assignments made there

#include <util/byte_operators.h>
#include <util/pointer_expr.h>
#include <util/find_symbols.h>

#include "assignments.h"
#include "ssa_dereference.h"
#include "local_ssa.h"

void assignmentst::build_assignment_map(
  const goto_programt &goto_program,
  const namespacet &ns)
{
  forall_goto_program_instructions(it, goto_program)
  {
    // make sure we have the location in the map
    assignment_map[it];

    // now fill it
    if(it->is_assign())
    {
      const code_assignt &code_assign=it->get_assign();
      exprt lhs_deref=dereference(
        code_assign.lhs(), ssa_value_ai[it], "", ns,
        options.get_bool_option("competition-mode"));
      assign(lhs_deref, it, ns);
      exprt lhs_symbolic_deref=symbolic_dereference(code_assign.lhs(), ns);
      assign(lhs_symbolic_deref, it, ns);

      assign_symbolic_rhs(code_assign.rhs(), it, ns);

      if(dynamic_objects.have_objects(*it))
      {
        // Create empty assignment into each new object (or into each of its
        // fields) so that it gets a non-deterministic value
        for(auto &dynobj : dynamic_objects.get_objects(*it))
        {
          ssa_objectt object(dynobj.symbol_expr(), ns);
          create_alloc_decl(object, dynobj.get_alloc_guard(), it, ns);
        }
      }
    }
    else if(it->is_assert())
    {
      assign_symbolic_rhs(it->guard, it, ns);
    }
    else if(it->is_decl())
    {
      const code_declt &code_decl=code_declt{it->decl_symbol()};
      assign(code_decl.symbol(), it, ns);
    }
    else if(it->is_function_call())
    {
      const code_function_callt &code_function_call=it->get_function_call();

      // Get information from ssa_heap_analysis
      auto n_it=it;
      ++n_it;
      const irep_idt fname=to_symbol_expr(
        code_function_call.function()).get_identifier();

      for(objectst::const_iterator
            o_it=ssa_objects.globals.begin();
          o_it!=ssa_objects.globals.end(); o_it++)
      {
        if(id2string(o_it->get_identifier())==id2string(fname)+"#return_value")
          assign(*o_it, it, ns);
      }

      // the call might come with an assignment
      if(code_function_call.lhs().is_not_nil())
      {
        exprt lhs_deref=
          dereference(
            code_function_call.lhs(), ssa_value_ai[it], "", ns,
            options.get_bool_option("competition-mode"));
        assign(lhs_deref, it, ns);
      }
    }
    else if(it->is_dead())
    {
    }
  }
}

void assignmentst::assign(
  const exprt &lhs,
  locationt loc,
  const namespacet &ns)
{
  if(is_symbol_struct_member(lhs, ns))
  {
    const typet &lhs_type=ns.follow(lhs.type());

    if(lhs_type.id()==ID_struct)
    {
      // Are we assigning an entire struct?
      // If so, need to split into pieces, recursively.

      const struct_typet &struct_type=to_struct_type(lhs_type);
      const struct_typet::componentst &components=struct_type.components();

      for(struct_typet::componentst::const_iterator
          it=components.begin();
          it!=components.end();
          it++)
      {
        member_exprt new_lhs(lhs, it->get_name(), it->type());
        assign(new_lhs, loc, ns); // recursive call
      }

      return; // done
    }

    // object?
    ssa_objectt ssa_object(lhs, ns);

    if(ssa_object)
    {
      assign(ssa_object, loc, ns);
    }

    return; // done
  }

  if(lhs.id()==ID_typecast)
  {
    assign(to_typecast_expr(lhs).op(), loc, ns);
  }
  else if(lhs.id()==ID_if)
  {
    assign(to_if_expr(lhs).true_case(), loc, ns);
    assign(to_if_expr(lhs).false_case(), loc, ns);
  }
  else if(lhs.id()==ID_index)
  {
    assign(to_index_expr(lhs).array(), loc, ns);
  }
  else if(lhs.id()==ID_member)
  {
    // non-flattened struct or union member
    const member_exprt &member_expr=to_member_expr(lhs);
    assign(member_expr.struct_op(), loc, ns);
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &byte_extract_expr=to_byte_extract_expr(lhs);

    assign(byte_extract_expr.op(), loc, ns);
  }
  else if(lhs.id()==ID_complex_real || lhs.id()==ID_complex_imag)
  {
    assert(lhs.operands().size()==1);
    assign(to_complex_real_expr(lhs).op(), loc, ns);
  }
}

void assignmentst::assign(
  const ssa_objectt &lhs,
  locationt loc,
  const namespacet &)
{
  assignment_map[loc].insert(lhs);
}

/// Adds to assignments dereferences from assertion
void assignmentst::assign_symbolic_rhs(
  const exprt &expr,
  const locationt &loc,
  const namespacet &ns)
{
  exprt rhs_symbolic_deref=symbolic_dereference(expr, ns);
  ssa_objectt rhs_object(rhs_symbolic_deref, ns);

  if(has_symbolic_deref(rhs_symbolic_deref) && rhs_object)
  {
    rhs_symbolic_deref.set("#is_rhs_assign", true);
    assign(rhs_symbolic_deref, loc, ns);
  }
  else if(has_symbolic_deref(rhs_symbolic_deref))
  {
    forall_operands(it, expr)
      assign_symbolic_rhs(*it, loc, ns);
  }
}

void assignmentst::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  std::ostream &out)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->source_location << "\n";

    assignment_mapt::const_iterator m_it=assignment_map.find(i_it);
    if(m_it==assignment_map.end())
      throw "location not found";

    const objectst &objects=m_it->second;

    for(objectst::const_iterator
        o_it=objects.begin();
        o_it!=objects.end();
        o_it++)
    {
      out << o_it->get_identifier() << "\n";
    }

    out << "\n";
  }
}

void assignmentst::create_alloc_decl(
  const ssa_objectt &object,
  const exprt &guard,
  const locationt loc,
  const namespacet &ns)
{
  auto &type=ns.follow(object.type());
  if(type.id()==ID_struct)
  {
    for(auto &c : to_struct_type(type).components())
    {
      ssa_objectt member(
        member_exprt(object.symbol_expr(), c.get_name(), c.type()), ns);
      create_alloc_decl(member, guard, loc, ns);
    }
    return;
  }

  alloc_guards_map.emplace(std::make_pair(loc, object), guard);
  assign(object, loc, ns);
}
