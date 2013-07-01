/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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

#include <iostream>

void function_SSAt::build_SSA()
{
  // collect objects
  collect_objects();
  
  // perform SSA data-flow analysis
  ssa_analysis(goto_function.body);

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
          
    if(p_it!=phi_nodes.end())
    {
      // yes
      const std::set<ssa_domaint::def_entryt> &incoming=p_it->second;

      exprt rhs=nil_exprt();
      bool has_backward=false;

      for(std::set<ssa_domaint::def_entryt>::const_iterator
          incoming_it=incoming.begin();
          incoming_it!=incoming.end();
          incoming_it++)
      {
        exprt incoming_value, incoming_guard;

        // we distinguish forwards- from brackwards-edges
        if(incoming_it->source->location_number > loc->location_number)
        {
          incoming_value=name(*o_it, LOOP, loc);
          incoming_guard=name(guard_symbol(), LOOP, loc);
          has_backward=true;
        }
        else
        {
          incoming_value=name(*o_it, OUT, incoming_it->def);
          incoming_guard=name(guard_symbol(), OUT, incoming_it->source);
        }

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
        equality.rhs()=read(code_assign.rhs(), loc);
    
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
            and_exprt(gs, read(i_it->guard, i_it)));
      }
      else if(next==loc && !i_it->guard.is_true())
        sources.push_back(
          and_exprt(gs, not_exprt(read(i_it->guard, i_it))));
    }
    else if(i_it->is_assume())
    {
      if(next==loc)
        sources.push_back(
          and_exprt(gs, read(i_it->guard, i_it)));
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
  
  exprt rhs;
  
  if(sources.empty())
    return;
  else if(sources.size()==1)
    rhs=sources.front();
  else
    rhs=or_exprt(sources);

  equal_exprt equality(name(guard_symbol(), OUT, loc), rhs);
  nodes[loc].equalities.push_back(equality);
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

Function: function_SSAt::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt function_SSAt::read(const exprt &expr, locationt loc) const
{
  if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol_expr=to_symbol_expr(expr);
    const irep_idt &identifier=symbol_expr.get_identifier();
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
      locationt def=d_it->second.def;
      
      // reading from PHI node or OUT?
      if(assigns(symbol_expr, def) && def!=loc)
        return name(to_symbol_expr(expr), OUT, def);
      else
        return name(to_symbol_expr(expr), PHI, def);
    }
  }
  else if(expr.id()==ID_address_of)
  {
    return expr;
  }
  else
  {
    exprt tmp=expr; // copy
    Forall_operands(it, tmp)
      *it=read(*it, loc);
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
  // kind IN means:
  // * LOOP if there is a LOOP node at loc for symbol
  // * OUT  otherwise
  
  if(kind==IN)
  {
    const ssa_domaint::phi_nodest &phi_nodes=ssa_analysis[loc].phi_nodes;

    ssa_domaint::phi_nodest::const_iterator p_it=
      phi_nodes.find(symbol.get_identifier());
      
    kind=OUT;
          
    if(p_it!=phi_nodes.end())
    {
      const std::set<ssa_domaint::def_entryt> &incoming=p_it->second;

      for(std::set<ssa_domaint::def_entryt>::const_iterator
          incoming_it=incoming.begin();
          incoming_it!=incoming.end();
          incoming_it++)
      {
        if(incoming_it->source->location_number > loc->location_number)
          kind=LOOP;
      }
    }
  }

  symbol_exprt new_symbol_expr=symbol; // copy
  const irep_idt &old_id=symbol.get_identifier();
  unsigned cnt=loc->location_number;
  irep_idt new_id=id2string(old_id)+"#"+
                  (kind==PHI?"phi":(kind==LOOP?"loop":""))+
                  i2string(cnt)+
                  suffix;
  new_symbol_expr.set_identifier(new_id);
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
    objects.insert(to_symbol_expr(src));
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

    out << "*** " << i_it->location << std::endl;
    n_it->second.output(out, ns);
    out << std::endl;
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
    out << from_expr(ns, "", *e_it) << std::endl;
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
  for(function_SSAt::nodest::const_iterator
      n_it=src.nodes.begin();
      n_it!=src.nodes.end();
      n_it++)
  {
    for(function_SSAt::nodet::equalitiest::const_iterator
        e_it=n_it->second.equalities.begin();
        e_it!=n_it->second.equalities.end();
        e_it++)
      dest << *e_it;
  }
  
  return dest;
}
  