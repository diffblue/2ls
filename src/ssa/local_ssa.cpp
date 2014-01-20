/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/i2string.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>

#include <langapi/language_util.h>

#include "object_id.h"
#include "local_ssa.h"

/*******************************************************************\

Function: local_SSAt::build_SSA

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::build_SSA()
{
  // collect objects
  collect_objects();
  
  // perform SSA data-flow analysis
  ssa_analysis(goto_function, ns);

  // now build phi-nodes
  forall_goto_program_instructions(i_it, goto_function.body)
    build_phi_nodes(i_it);
  
  // now build transfer functions
  forall_goto_program_instructions(i_it, goto_function.body)
    build_transfer(i_it);

  // now build guards
  forall_goto_program_instructions(i_it, goto_function.body)
    build_guard(i_it);
}

/*******************************************************************\

Function: local_SSAt::build_phi_nodes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::build_phi_nodes(locationt loc)
{
  const ssa_domaint::phi_nodest &phi_nodes=ssa_analysis[loc].phi_nodes;
  nodet &node=nodes[loc];

  for(objectst::const_iterator
      o_it=objects.begin(); o_it!=objects.end(); o_it++)
  {
    // phi-node here?
    ssa_domaint::phi_nodest::const_iterator p_it=
      phi_nodes.find(o_it->get_identifier());
          
    if(p_it==phi_nodes.end()) continue; // none
    
    // yes
    // source -> def map
    const std::map<locationt, ssa_domaint::deft> &incoming=p_it->second;

    exprt rhs=nil_exprt();

    // We distinguish forwards- from backwards-edges,
    // and do forwards-edges first, which gives them
    // _lower_ priority in the ITE. Inputs are always
    // forward edges.
    
    for(std::map<locationt, ssa_domaint::deft>::const_iterator
        incoming_it=incoming.begin();
        incoming_it!=incoming.end();
        incoming_it++)
      if(incoming_it->second.is_input() ||
         incoming_it->first->location_number < loc->location_number)
      {
        // it's a forward edge
        exprt incoming_value=name(*o_it, incoming_it->second);
        exprt incoming_guard=guard_symbol(incoming_it->first);

        if(rhs.is_nil()) // first
          rhs=incoming_value;
        else
          rhs=if_exprt(incoming_guard, incoming_value, rhs);
      }
     
    // now do backwards

    for(std::map<locationt, ssa_domaint::deft>::const_iterator
        incoming_it=incoming.begin();
        incoming_it!=incoming.end();
        incoming_it++)
      if(!incoming_it->second.is_input() &&
         incoming_it->first->location_number >= loc->location_number)
      {
        // it's a backwards edge
        exprt incoming_value=name(*o_it, LOOP_BACK, incoming_it->first);
        exprt incoming_select=name(guard_symbol(), LOOP_SELECT, incoming_it->first);

        if(rhs.is_nil()) // first
          rhs=incoming_value;
        else
          rhs=if_exprt(incoming_select, incoming_value, rhs);
      }

    symbol_exprt lhs=name(*o_it, PHI, loc);
    
    equal_exprt equality(lhs, rhs);
    node.equalities.push_back(equality);
  }
}

/*******************************************************************\

Function: local_SSAt::assigns

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool local_SSAt::assigns(const objectt &object, locationt loc) const
{
  if(loc->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(loc->code);
    return assigns_rec(object, code_assign.lhs());
  }
  else if(loc->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(loc->code);

    if(code_function_call.lhs().is_nil())
      return false;
      
    return assigns_rec(object, code_function_call.lhs());
  }
  else if(loc->is_decl())
  {
    const code_declt &code_decl=to_code_decl(loc->code);
    return assigns_rec(object, code_decl.symbol());
  }
  else
    return false;
}

/*******************************************************************\

Function: local_SSAt::assigns_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool local_SSAt::assigns_rec(
  const objectt &object,
  const exprt &lhs) const
{
  const typet &type=ns.follow(lhs.type());

  if(type.id()==ID_struct)
  {
    // need to split up

    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      member_exprt new_lhs(lhs, it->get_name(), it->type());
      if(assigns_rec(object, new_lhs)) // recursive call
        return true;
    }
    
    return false; // done
  }
  else
    return lhs==object.get_expr();
}

/*******************************************************************\

Function: local_SSAt::build_transfer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::build_transfer(locationt loc)
{
  if(loc->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(loc->code);

    assign_rec(code_assign.lhs(), code_assign.rhs(), loc);
  }
  else if(loc->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(loc->code);

    if(code_function_call.lhs().is_not_nil())
    {
    }
  }
}
  
/*******************************************************************\

Function: local_SSAt::build_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::build_guard(locationt loc)
{
  const guard_mapt::entryt &entry=guard_map[loc];
  
  // anything to be built?
  if(!entry.has_guard) return;
  
  exprt::operandst sources;

  // the very first 'loc' trivially gets 'true' as source
  if(loc==goto_function.body.instructions.begin())
    sources.push_back(true_exprt());

  for(guard_mapt::incomingt::const_iterator
      i_it=entry.incoming.begin();
      i_it!=entry.incoming.end();
      i_it++)
  {
    const guard_mapt::edget &edge=*i_it;
    
    if(edge.guard.is_false()) continue;
    
    exprt source;
    
    // might be backwards
    if(edge.from->is_backwards_goto())
    {
      symbol_exprt loop_select=
        name(guard_symbol(), LOOP_SELECT, edge.guard_source);

      source=loop_select;
      // need constraing for edge.cond
    }
    else
    {
      symbol_exprt gs=name(guard_symbol(), OUT, edge.guard_source);
      source=and_exprt(gs, read_rhs(edge.guard, edge.from));
    }
    
    sources.push_back(source);
  }

  // the below produces 'false' if there is no source
  exprt rhs=disjunction(sources);
  
  equal_exprt equality(guard_symbol(loc), rhs);
  nodes[loc].equalities.push_back(equality);
}

/*******************************************************************\

Function: local_SSAt::assertions_to_constraints

  Inputs:

 Outputs:

 Purpose: turns assertions into constraints

\*******************************************************************/

void local_SSAt::assertions_to_constraints()
{
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_assert())
    {
      exprt c=read_rhs(i_it->guard, i_it);
      exprt g=guard_symbol(i_it);
      implies_exprt implication(g, c);
      nodes[i_it].constraints.push_back(implication);
    }
  }  
}

/*******************************************************************\

Function: local_SSAt::guard_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

local_SSAt::objectt local_SSAt::guard_symbol()
{
  return objectt(symbol_exprt("ssa::$guard", bool_typet()));
}

/*******************************************************************\

Function: local_SSAt::read_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt local_SSAt::read_rhs(
  const objectt &object,
  locationt loc) const
{
  const irep_idt &identifier=object_id(object.get_expr());
  const ssa_domaint &ssa_domain=ssa_analysis[loc];

  ssa_domaint::def_mapt::const_iterator d_it=
    ssa_domain.def_map.find(identifier);

  if(d_it==ssa_domain.def_map.end())
  {
    // not written so far, it's input
    return name_input(object);
  }
  else
    return name(object, d_it->second.def);
}

/*******************************************************************\

Function: local_SSAt::read_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt local_SSAt::read_lhs(
  const exprt &expr,
  locationt loc) const
{
  objectt object(expr);

  // is this an object we track?
  if(objects.find(object)!=objects.end())
  {
    // yes, it is
    if(assigns(object, loc))
      return name(object, OUT, loc);
    else
      return read_rhs(object, loc);
  }
  else
    return read_rhs(expr, loc);
}

/*******************************************************************\

Function: local_SSAt::read_node_in

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt local_SSAt::read_node_in(
  const objectt &object,
  locationt loc) const
{
  // This reads:
  // * LOOP_BACK if there is a LOOP node at 'loc' for symbol
  // * OUT otherwise

  const irep_idt &identifier=object_id(object.get_expr());
  const ssa_domaint &ssa_domain=ssa_analysis[loc];

  ssa_domaint::def_mapt::const_iterator d_it=
    ssa_domain.def_map.find(identifier);

  if(d_it==ssa_domain.def_map.end())
    return name_input(object); // not written so far

  const ssa_domaint::phi_nodest &phi_nodes=ssa_analysis[loc].phi_nodes;

  ssa_domaint::phi_nodest::const_iterator p_it=
    phi_nodes.find(identifier);
    
  bool has_phi=false;
        
  if(p_it!=phi_nodes.end())
  {
    const std::map<locationt, ssa_domaint::deft> &incoming=p_it->second;

    for(std::map<locationt, ssa_domaint::deft>::const_iterator
        incoming_it=incoming.begin();
        incoming_it!=incoming.end();
        incoming_it++)
    {
      if(incoming_it->first->location_number > loc->location_number)
        has_phi=true;
    }
  }
  
  if(has_phi)
    return name(object, LOOP_BACK, loc);
  else
    return read_rhs(object, loc);
}

/*******************************************************************\

Function: local_SSAt::read_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt local_SSAt::read_rhs(const exprt &expr, locationt loc) const
{
  objectt object(expr);

  // is this an object we track?
  if(objects.find(object)!=objects.end())
    return read_rhs(object, loc);
  else if(expr.id()==ID_symbol)
    return name_input(object);
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt address_of_expr=to_address_of_expr(expr);
    return address_of_expr;
  }
  else
  {
    exprt tmp=expr; // copy
    Forall_operands(it, tmp)
      *it=read_rhs(*it, loc);
    return tmp;
  }
}

/*******************************************************************\

Function: local_SSAt::name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt local_SSAt::name(
  const objectt &object,
  kindt kind,
  locationt loc) const
{
  symbol_exprt new_symbol_expr(object.get_expr().type());
  const irep_idt &id=object.get_identifier();
  unsigned cnt=loc->location_number;
  
  irep_idt new_id=id2string(id)+"#"+
                  (kind==PHI?"phi":
                   kind==LOOP_BACK?"lb":
                   kind==LOOP_SELECT?"ls":
                   "")+
                  i2string(cnt)+
                  (kind==LOOP_SELECT?std::string(""):suffix);

  new_symbol_expr.set_identifier(new_id);
  
  if(object.get_expr().location().is_not_nil())
    new_symbol_expr.location()=object.get_expr().location();
  
  return new_symbol_expr;
}

/*******************************************************************\

Function: local_SSAt::name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt local_SSAt::name(
  const objectt &object,
  const ssa_domaint::deft &def) const
{
  if(def.kind==ssa_domaint::deft::INPUT)
    return name_input(object);
  else if(def.kind==ssa_domaint::deft::PHI)
    return name(object, PHI, def.loc);
  else
    return name(object, OUT, def.loc);
}

/*******************************************************************\

Function: local_SSAt::name_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt local_SSAt::name_input(const objectt &object) const
{
  symbol_exprt new_symbol_expr(object.get_expr().type()); // copy
  const irep_idt old_id=object.get_identifier();
  irep_idt new_id=id2string(old_id)+suffix;
  new_symbol_expr.set_identifier(new_id);

  if(object.get_expr().location().is_not_nil())
    new_symbol_expr.location()=object.get_expr().location();

  return new_symbol_expr;
}

/*******************************************************************\

Function: local_SSAt::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::assign_rec(
  const exprt &lhs,
  const exprt &rhs,
  locationt loc)
{
  const typet &type=ns.follow(lhs.type());

  if(type.id()==ID_struct)
  {
    // need to split up

    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      member_exprt new_lhs(lhs, it->get_name(), it->type());
      member_exprt new_rhs(rhs, it->get_name(), it->type());
      assign_rec(new_lhs, new_rhs, loc);
    }
    
    return; // done
  }

  objectt lhs_object(lhs);

  // is this an object we track?
  if(objects.find(lhs_object)!=objects.end())
  {
    // yes!
    const symbol_exprt ssa_symbol=name(lhs_object, OUT, loc);
    exprt ssa_rhs=read_rhs(rhs, loc);
    equal_exprt equality(ssa_symbol, ssa_rhs);

    nodes[loc].equalities.push_back(equality);
  }
}

/*******************************************************************\

Function: local_SSAt::collect_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::collect_objects_rec(const exprt &src)
{
  const typet &type=ns.follow(src.type());

  if(type.id()==ID_code)
    return;

  if(type.id()==ID_struct)
  {
    // need to split up

    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
    
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      member_exprt new_src(src, it->get_name(), it->type());
      collect_objects_rec(new_src); // recursive call
    }
    
    return; // done
  }

  irep_idt id=object_id(src);
  
  if(id!=irep_idt())
    objects.insert(objectt(src));
  else
  {
    forall_operands(it, src)
      collect_objects_rec(*it);
  }
}

/*******************************************************************\

Function: local_SSAt::collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::collect_objects()
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    collect_objects_rec(it->guard);
    collect_objects_rec(it->code);
  }
}

/*******************************************************************\

Function: local_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::output(std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    const nodest::const_iterator n_it=nodes.find(i_it);
    if(n_it==nodes.end()) continue;
    if(n_it->second.empty()) continue;

    out << "*** " << i_it->location_number
        << " " << i_it->location << "\n";
    n_it->second.output(out, ns);
    out << "\n";
  }
}

/*******************************************************************\

Function: local_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::nodet::output(
  std::ostream &out,
  const namespacet &ns) const
{
  for(equalitiest::const_iterator
      e_it=equalities.begin();
      e_it!=equalities.end();
      e_it++)
    out << from_expr(ns, "", *e_it) << "\n";

  for(constraintst::const_iterator
      e_it=constraints.begin();
      e_it!=constraints.end();
      e_it++)
    out << from_expr(ns, "", *e_it) << "\n";

}

/*******************************************************************\

Function: local_SSAt::has_static_lifetime

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool local_SSAt::has_static_lifetime(const objectt &object) const
{
  return has_static_lifetime(object.get_expr());
}

/*******************************************************************\

Function: local_SSAt::has_static_lifetime

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool local_SSAt::has_static_lifetime(const exprt &src) const
{
  if(src.id()==ID_dereference)
    return true;
  else if(src.id()==ID_index)
    return has_static_lifetime(to_index_expr(src).array());
  else if(src.id()==ID_member)
    return has_static_lifetime(to_member_expr(src).struct_op());
  else if(src.id()==ID_symbol)
  {
    const symbolt &s=ns.lookup(to_symbol_expr(src));
    return s.is_static_lifetime;
  }
  else
    return false;
}

/*******************************************************************\

Function: local_SSAt::operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::list<exprt> & operator << (
  std::list<exprt> &dest,
  const local_SSAt &src)
{
  forall_goto_program_instructions(i_it, src.goto_function.body)
  {
    const local_SSAt::nodest::const_iterator n_it=
      src.nodes.find(i_it);
    if(n_it==src.nodes.end()) continue;

    for(local_SSAt::nodet::equalitiest::const_iterator
        e_it=n_it->second.equalities.begin();
        e_it!=n_it->second.equalities.end();
        e_it++)
    {
      dest.push_back(*e_it);
    }

    for(local_SSAt::nodet::constraintst::const_iterator
        c_it=n_it->second.constraints.begin();
        c_it!=n_it->second.constraints.end();
        c_it++)
    {
      dest.push_back(*c_it);
    }
  }
  
  return dest;
}
