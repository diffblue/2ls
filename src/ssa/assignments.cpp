/*******************************************************************\

Module: A map of program locations to the assignments made there

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "assignments.h"

/*******************************************************************\

Function: assignmentst::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void assignmentst::build(
  const goto_programt &goto_program,
  const namespacet &ns)
{
  collect_objects(goto_program, ns, objects);

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
      const code_function_callt &code_fc=to_code_function_call(it->code);
      assign(code_fc.lhs(), it, ns);
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
  const exprt &lhs, goto_programt::const_targett loc,
  const namespacet &ns)
{
  if(lhs.id()==ID_typecast)
  {
    assign(to_typecast_expr(lhs).op(), loc, ns);
    return;
  }
  else if(lhs.id()==ID_if)
  {
    assign(to_if_expr(lhs).true_case(), loc, ns);
    assign(to_if_expr(lhs).false_case(), loc, ns);
    return;
  }
  else if(lhs.id()==ID_index)
  {
    assign(to_index_expr(lhs).array(), loc, ns);
    return;
  }

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
  else if(lhs_type.id()==ID_union)
  {
    // todo
  }

  const ssa_objectt ssa_object(lhs);
  
  if(ssa_object)
  {
    assign(ssa_object, loc, ns);

    if(lhs.id()==ID_dereference)
    {
      // this might alias other stuff
      for(std::set<ssa_objectt>::const_iterator
          o_it=objects.begin();
          o_it!=objects.end();
          o_it++)
      {
        if(*o_it!=ssa_object &&
           may_alias(*o_it, ssa_object))
          assign(*o_it, loc, ns);
      }
    }    
  }
}

/*******************************************************************\

Function: assignmentst::may_alias

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool assignmentst::may_alias(
  const ssa_objectt &o1, const ssa_objectt &o2)
{
  const exprt &e1=o1.get_expr();
  const exprt &e2=o2.get_expr();

  // The same?
  if(e1==e2)
    return true;

  // Is one a pointer?
  if(e1.id()==ID_dereference || e2.id()==ID_dereference)
  {
    // Type matches?
    if(e1.type()==e2.type())
      return true;
    
    // Give up, but should consider more options
    return false;
  }
  else
    return false; // both different objects
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
