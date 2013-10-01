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

#include "function_ssa.h"

/*******************************************************************\

Function: function_SSAt::build_SSA

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_SSA()
{
  // collect objects
  collect_objects();
  
  // perform SSA data-flow analysis
  ssa_analysis(goto_function);

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

Function: function_SSAt::build_phi_nodes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_phi_nodes(locationt loc)
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
        exprt incoming_value=name(*o_it, LOOP, loc);
        exprt incoming_guard=name(guard_symbol(), LOOP, loc);

        if(rhs.is_nil()) // first
          rhs=incoming_value;
        else
          rhs=if_exprt(incoming_guard, incoming_value, rhs);
      }

    symbol_exprt lhs=name(*o_it, PHI, loc);
    
    equal_exprt equality(lhs, rhs);
    node.equalities.push_back(equality);
  }
}

/*******************************************************************\

Function: function_SSAt::assigns

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool function_SSAt::assigns(const symbol_exprt &object, locationt loc) const
{
  if(loc->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(loc->code);
    return code_assign.lhs()==object;
  }
  else if(loc->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(loc->code);

    if(code_function_call.lhs().is_nil())
      return false;
      
    return code_function_call.lhs()==object;
  }
  else if(loc->is_decl())
  {
    const code_declt &code_decl=to_code_decl(loc->code);
    return code_decl.symbol()==object;
  }
  else
    return false;
}

/*******************************************************************\

Function: function_SSAt::build_transfer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_transfer(locationt loc)
{
  nodet &node=nodes[loc];

  for(objectst::const_iterator
      o_it=objects.begin(); o_it!=objects.end(); o_it++)
  {
    // assigned here?
    if(assigns(*o_it, loc))
    {
      if(loc->is_assign())
      {
        const code_assignt &code_assign=to_code_assign(loc->code);
        
        equal_exprt equality;
        equality.lhs()=name(*o_it, OUT, loc);
        equality.rhs()=read_rhs(code_assign.rhs(), loc);
    
        node.equalities.push_back(equality);
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
  }
}
  
/*******************************************************************\

Function: function_SSAt::build_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_guard(locationt loc)
{
  exprt::operandst sources;

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    locationt next=i_it;
    next++;
    
    symbol_exprt gs=name(guard_symbol(), OUT, i_it);
    
    if(i_it->is_goto())
    {
      // target, perhaps?
      if(i_it->get_target()==loc)
      {
        // Yes. Might be backwards.
        if(i_it->is_backwards_goto())
          sources.push_back(
            name(guard_symbol(), LOOP, loc));
        else
          sources.push_back(
            and_exprt(gs, read_rhs(i_it->guard, i_it)));
      }
      else if(next==loc && !i_it->guard.is_true())
        sources.push_back(
          and_exprt(gs, not_exprt(read_rhs(i_it->guard, i_it))));
    }
    else if(i_it->is_assume())
    {
      if(next==loc)
        sources.push_back(
          and_exprt(gs, read_rhs(i_it->guard, i_it)));
    }
    else if(i_it->is_return() || i_it->is_throw())
    {
    }
    else
    {
      if(next==loc)
        sources.push_back(gs);
    }
  }
  
  if(sources.empty())
    return;

  exprt rhs=disjunction(sources);

  equal_exprt equality(name(guard_symbol(), OUT, loc), rhs);
  nodes[loc].equalities.push_back(equality);
}

/*******************************************************************\

Function: function_SSAt::assertions_to_constraints

  Inputs:

 Outputs:

 Purpose: turns assertions into constraints

\*******************************************************************/

void function_SSAt::assertions_to_constraints()
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

Function: function_SSAt::guard_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::guard_symbol()
{
  return symbol_exprt("ssa::$guard", bool_typet());
}

/*******************************************************************\

Function: function_SSAt::read_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::read_rhs(
  const symbol_exprt &expr,
  locationt loc) const
{
  const irep_idt &identifier=expr.get_identifier();
  const ssa_domaint &ssa_domain=ssa_analysis[loc];

  ssa_domaint::def_mapt::const_iterator d_it=
    ssa_domain.def_map.find(identifier);

  if(d_it==ssa_domain.def_map.end())
  {
    // not written so far, it's input
    return name_input(expr);
  }
  else
    return name(expr, d_it->second.def);
}

/*******************************************************************\

Function: function_SSAt::read_lhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt function_SSAt::read_lhs(
  const exprt &expr,
  locationt loc) const
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    if(assigns(symbol_expr, loc))
      return name(symbol_expr, OUT, loc);
    else
      return read_rhs(symbol_expr, loc);
  }
  else if(expr.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(expr);
    tmp.struct_op()=read_lhs(tmp.struct_op(), loc);
    return tmp;
  }
  else if(expr.id()==ID_index)
  {
    index_exprt tmp=to_index_expr(expr);
    tmp.array()=read_lhs(tmp.array(), loc);
    return tmp;
  }
  else
    return read_rhs(expr, loc);
}

/*******************************************************************\

Function: function_SSAt::read_in

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::read_in(
  const symbol_exprt &expr,
  locationt loc) const
{
  // This reads:
  // * LOOP if there is a LOOP node at 'loc' for symbol
  // * OUT  otherwise

  const irep_idt &identifier=expr.get_identifier();
  const ssa_domaint &ssa_domain=ssa_analysis[loc];

  ssa_domaint::def_mapt::const_iterator d_it=
    ssa_domain.def_map.find(identifier);

  if(d_it==ssa_domain.def_map.end())
  {
    // not written so far
    return expr;
  }
  else
  {
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
      return name(expr, LOOP, loc);
    else
      return read_rhs(expr, loc);
  }
}

/*******************************************************************\

Function: function_SSAt::read_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt function_SSAt::read_rhs(const exprt &expr, locationt loc) const
{
  if(expr.id()==ID_symbol)
    return read_rhs(to_symbol_expr(expr), loc);
  else if(expr.id()==ID_address_of)
  {
    return expr;
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

Function: function_SSAt::name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::name(
  const symbol_exprt &symbol,
  kindt kind,
  locationt loc) const
{
  symbol_exprt new_symbol_expr=symbol; // copy
  const irep_idt &old_id=symbol.get_identifier();
  unsigned cnt=loc->location_number;

  irep_idt new_id=id2string(old_id)+"#"+
                  (kind==PHI?"phi":(kind==LOOP?"loop":""))+
                  i2string(cnt)+
                  suffix;

  new_symbol_expr.set_identifier(new_id);
  
  if(symbol.location().is_not_nil())
    new_symbol_expr.location()=symbol.location();
  
  return new_symbol_expr;
}

/*******************************************************************\

Function: function_SSAt::name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::name(
  const symbol_exprt &symbol_expr,
  const ssa_domaint::deft &def) const
{
  if(def.kind==ssa_domaint::deft::INPUT)
    return name_input(symbol_expr);
  else if(def.kind==ssa_domaint::deft::PHI)
    return name(symbol_expr, PHI, def.loc);
  else
    return name(symbol_expr, OUT, def.loc);
}

/*******************************************************************\

Function: function_SSAt::name_input

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::name_input(const symbol_exprt &symbol) const
{
  symbol_exprt new_symbol_expr=symbol; // copy
  const irep_idt &old_id=symbol.get_identifier();
  irep_idt new_id=id2string(old_id)+suffix;
  new_symbol_expr.set_identifier(new_id);

  if(symbol.location().is_not_nil())
    new_symbol_expr.location()=symbol.location();

  return new_symbol_expr;
}

/*******************************************************************\

Function: 

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
exprt function_SSAt::assign(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    const irep_idt &old_id=to_symbol_expr(expr).get_identifier();
    ++ssa_map[old_id];
    return rename(expr);
  }
  else if(expr.id()==ID_index)
  {
    index_exprt index_expr=to_index_expr(expr); // copy
    index_expr.index()=rename(index_expr.index());
    index_expr.array()=assign(index_expr.array());
    return index_expr;
  }
  else if(expr.id()==ID_member)
  {
    member_exprt member_expr=to_member_expr(expr); // copy
    member_expr.struct_op()=assign(member_expr.struct_op());
    return member_expr;
  }
  else if(expr.id()==ID_dereference)
  {
    dereference_exprt dereference_expr=to_dereference_expr(expr); // copy
    
    dereference_expr.pointer()=rename(dereference_expr.pointer());

    return dereference_expr;
  }
  else if(expr.id()==ID_typecast)
  {
    typecast_exprt typecast_expr=to_typecast_expr(expr); //copy
    typecast_expr.op()=assign(typecast_expr.op());
    return typecast_expr;
  }
  else
    return expr;
}
#endif

/*******************************************************************\

Function: function_SSAt::collect_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::collect_objects_rec(const exprt &src)
{
  forall_operands(it, src)
    collect_objects_rec(*it);
  
  if(src.id()==ID_symbol)
  {
    const typet &type=ns.follow(src.type());

    if(type.id()==ID_code)
    {
    }
    else
      objects.insert(to_symbol_expr(src));
  }
}

/*******************************************************************\

Function: function_SSAt::collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::collect_objects()
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    collect_objects_rec(it->guard);
    collect_objects_rec(it->code);
  }
}

/*******************************************************************\

Function: function_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::output(std::ostream &out) const
{
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    const nodest::const_iterator n_it=nodes.find(i_it);
    if(n_it==nodes.end()) continue;

    out << "*** " << i_it->location_number
        << " " << i_it->location << "\n";
    n_it->second.output(out, ns);
    out << "\n";
  }
}

/*******************************************************************\

Function: function_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::nodet::output(
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

Function: function_SSAt::operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret & operator << (
  decision_proceduret &dest,
  const function_SSAt &src)
{
  forall_goto_program_instructions(i_it, src.goto_function.body)
  {
    const function_SSAt::nodest::const_iterator n_it=
      src.nodes.find(i_it);
    if(n_it==src.nodes.end()) continue;

    for(function_SSAt::nodet::equalitiest::const_iterator
        e_it=n_it->second.equalities.begin();
        e_it!=n_it->second.equalities.end();
        e_it++)
    {
      dest << *e_it;
    }

    for(function_SSAt::nodet::constraintst::const_iterator
        c_it=n_it->second.constraints.begin();
        c_it!=n_it->second.constraints.end();
        c_it++)
    {
      dest << *c_it;
    }
  }
  
  return dest;
}
