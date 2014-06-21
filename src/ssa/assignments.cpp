/*******************************************************************\

Module: A map of program locations to the assignments made there

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "assignments.h"
#include "ssa_aliasing.h"

/*******************************************************************\

Function: assignmentst::build_assignment_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
      assign(code_assign.lhs(), it, ns);
    }
    else if(it->is_decl())
    {
      const code_declt &code_decl=to_code_decl(it->code);
      assign(code_decl.symbol(), it, ns);
    }
    else if(it->is_function_call())
    {
      const code_function_callt &code_function_call=to_code_function_call(it->code);

      // functions may alter state almost arbitrarily:
      // * any global-scoped variables
      // * any dirty locals
      
      for(objectst::const_iterator
          o_it=ssa_objects.dirty_locals.begin();
          o_it!=ssa_objects.dirty_locals.end(); o_it++)
        assign(*o_it, it, ns);

      for(objectst::const_iterator
          o_it=ssa_objects.globals.begin();
          o_it!=ssa_objects.globals.end(); o_it++)
        assign(*o_it, it, ns);

      // the call might come with an assignment
      if(code_function_call.lhs().is_not_nil())
        assign(code_function_call.lhs(), it, ns);
    }
    else if(it->is_dead())
    {
    }
  }
}

/*******************************************************************\

Function: assignmentst::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void assignmentst::assign(
  const exprt &lhs,
  goto_programt::const_targett loc,
  const namespacet &ns)
{
  if(is_symbol_or_deref_struct_member(lhs, ns))
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
    
    // this might alias all sorts of stuff
    for(std::set<ssa_objectt>::const_iterator
        o_it=ssa_objects.objects.begin();
        o_it!=ssa_objects.objects.end();
        o_it++)
    {
      if(ssa_may_alias(o_it->get_expr(), lhs, ns))
        assign(*o_it, loc, ns);
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
}

/*******************************************************************\

Function: assignmentst::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void assignmentst::assign(
  const ssa_objectt &lhs,
  goto_programt::const_targett loc,
  const namespacet &)
{
  assignment_map[loc].insert(lhs);
}

/*******************************************************************\

Function: assignmentst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void assignmentst::output(
  const namespacet &ns,
  const goto_programt &goto_program,
  std::ostream &out)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    out << "**** " << i_it->location_number << " "
        << i_it->location << "\n";
    
    assignment_mapt::const_iterator m_it=assignment_map.find(i_it);
    if(m_it==assignment_map.end()) throw "location not found";
    
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
