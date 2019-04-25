/*******************************************************************\

Module: A map of program locations to the assignments made there

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// A map of program locations to the assignments made there

#include <util/byte_operators.h>
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
      const code_assignt &code_assign=to_code_assign(it->code);
      exprt lhs_deref=dereference(code_assign.lhs(), ssa_value_ai[it], "", ns);
      assign(lhs_deref, it, ns);
      exprt lhs_symbolic_deref=symbolic_dereference(code_assign.lhs(), ns);
      assign(lhs_symbolic_deref, it, ns);

      assign_symbolic_rhs(code_assign.rhs(), it, ns);

      if(code_assign.rhs().get_bool("#malloc_result"))
      {
        // Create empty assignment into the object (declaration) so that it
        // gets non-deterministic value
        create_alloc_decl(code_assign.rhs(), true_exprt(), it, ns);
      }
    }
    else if(it->is_assert())
    {
      assign_symbolic_rhs(it->guard, it, ns);
    }
    else if(it->is_decl())
    {
      const code_declt &code_decl=to_code_decl(it->code);
      assign(code_decl.symbol(), it, ns);
    }
    else if(it->is_function_call())
    {
      const code_function_callt &code_function_call=
        to_code_function_call(it->code);

      // Get information from ssa_heap_analysis
      auto n_it=it;
      ++n_it;
      const irep_idt fname=to_symbol_expr(
        code_function_call.function()).get_identifier();
      std::list<symbol_exprt> new_objects;
      std::set<exprt> modified_objects;

      if(ssa_heap_analysis.has_location(n_it))
      {
        new_objects=ssa_heap_analysis[n_it].new_caller_objects(fname, it);
        modified_objects=ssa_heap_analysis[n_it].modified_objects(fname);
      }

      // Assign new objects
      for(auto &o : new_objects)
      {
        assign(o, it, ns);
      }

      for(objectst::const_iterator
            o_it=ssa_objects.globals.begin();
          o_it!=ssa_objects.globals.end(); o_it++)
      {
        if(id2string(o_it->get_identifier())==id2string(fname)+"#return_value")
          assign(*o_it, it, ns);
      }

      // Assign all modified objects
      for(const exprt &modified : modified_objects)
      {
        const exprt arg=
          ssa_heap_analysis[n_it].function_map.at(fname).
            corresponding_expr(modified, code_function_call.arguments(), 0);

        if(arg!=modified)
        {
          const exprt arg_deref=dereference(arg, ssa_value_ai[it], "", ns);
          assign(arg_deref, it, ns);

          std::set<symbol_exprt> symbols;
          find_symbols(arg_deref, symbols);
          for(const symbol_exprt &symbol : symbols)
          {
            if(symbol.type()==arg_deref.type())
            {
              auto &aliases=ssa_value_ai[n_it](symbol, ns).value_set;
              for(auto &alias : aliases)
              {
                assign(alias.get_expr(), it, ns);
              }
            }
          }
        }
      }

      // the call might come with an assignment
      if(code_function_call.lhs().is_not_nil())
      {
        exprt lhs_deref=
          dereference(code_function_call.lhs(), ssa_value_ai[it], "", ns);
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

    if(ssa_object &&
       !ssa_object.is_unknown_obj())  // unknown objects are just placeholders
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
    assign(lhs.op0(), loc, ns);
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

/// Create new fresh symbol for each object (and for each its field) dynamically
/// allocated at the given location.
void assignmentst::create_alloc_decl(
  const exprt &expr,
  const exprt &guard,
  const locationt loc,
  const namespacet &ns)
{
  if(expr.id()==ID_symbol || expr.id()==ID_member)
  {
    const typet &type=ns.follow(expr.type());
    if(type.id()==ID_struct)
    {
      for(auto &c : to_struct_type(type).components())
      {
        create_alloc_decl(
          member_exprt(expr, c.get_name(), c.type()), guard, loc, ns);
      }
    }
    else
    {
      ssa_objectt ssa_object(expr, ns);
      if(ssa_object)
      {
        // Create declaration
        assign(ssa_object, loc, ns);
        // Store allocation guard
        alloc_guards_map.emplace(std::make_pair(loc, ssa_object), guard);
      }
    }
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);
    create_alloc_decl(
      if_expr.true_case(),
      and_exprt(guard, if_expr.cond()),
      loc,
      ns);
    create_alloc_decl(
      if_expr.false_case(),
      and_exprt(guard, not_exprt(if_expr.cond())),
      loc,
      ns);
  }
  else if(expr.id()==ID_address_of)
    create_alloc_decl(
      to_address_of_expr(expr).object(), guard, loc, ns);
  else if(expr.id()==ID_typecast)
    create_alloc_decl(
      to_typecast_expr(expr).op(), guard, loc, ns);
}
