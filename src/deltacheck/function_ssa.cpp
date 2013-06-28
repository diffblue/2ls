/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>
#include <util/expr_util.h>
#include <util/union_find.h>

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
  static_analysist<ssa_domaint> ssa_analysis(ns);
  ssa_analysis(goto_function.body);

  // now build phi-nodes
  forall_goto_program_instructions(i_it, goto_function.body)
    build_phi_nodes(i_it);
  
  // now build transfer functions
  forall_goto_program_instructions(i_it, goto_function.body)
    build_transfer(i_it);
}

/*******************************************************************\

Function: function_SSAt::build_phi_nodes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_phi_nodes(locationt loc)
{
  const std::set<irep_idt> &phi_nodes=ssa_analysis[i_it].phi_nodes;
  nodet &node=nodes[loc];

  for(objectst::const_iterator
      o_it=objects.begin(); o_it!=objects.end(); o_it++)
  {
    // phi-node here?
    if(phi_nodes.find(o_it->get_identifier())!=phi_nodes.end())
    {
      // yes
      equal_exprt equality;
      equality.lhs()=name(*o_it, PHI, loc)
      
      node.equalities.push_back(
    }
  }
}

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
  static_analysist<ssa_domaint> ssa_analysis(ns);
  ssa_analysis(goto_function.body);

  // now build phi-nodes
  forall_goto_program_instructions(i_it, goto_function.body)
    phi_nodes(i_it);
  
  // now build transfer functions
  forall_goto_program_instructions(i_it, goto_function.body)
    transfer(i_it);
  
  {
    def_mapt &def_map=ssa_analysis[i_it].def_map;
    nodet &node=nodes[i_it];
  
    for(objectst::const_iterator
        o_it=objects.begin(); o_it!=objects.end(); o_it++)
    {
      irep_idt &identifier=o_it->get_identifier();
      
      // phi-node?
      ssa_domaint::def_mapt::const_iterator d_it=
        def_map.find(identifier);
        
      if(d_it!=def_map.end() && d_it->second==i_it)
      {
        // yes
        
      }
      
      // written here?
      if(i_it->is_assign())
      {
      }
    }
  }
}

/*******************************************************************\

Function: function_SSAt::build_outgoing

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_outgoing()
{
  // now build formulas for outgoing data-flow
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    for(objectst::const_iterator
        o_it=objects.begin(); o_it!=objects.end(); o_it++)
    {
      exprt incoming_value=name(*o_it, IN, i_it);
      exprt rhs=incoming_value;
      
      if(i_it->is_assign())
      {
        const code_assignt &code_assign=to_code_assign(i_it->code);
        if(code_assign.lhs()==*o_it)
          rhs=rename(code_assign.rhs(), IN, i_it);
      }
      else if(i_it->is_function_call())
      {
        const code_function_callt &code_function_call=
          to_code_function_call(i_it->code);

        if(code_function_call.lhs().is_not_nil())
        {
          #if 0
          nodes.push_back(nodet());
          nodet &n=nodes.back();
          n.guard=rename(guard);

          // order matters here, RHS is done before LHS
          n.equality.rhs()=rename(code_assign.rhs());
          n.equality.lhs()=assign(code_function_call.lhs());
          #endif
        }
      }

      symbol_exprt lhs=name(*o_it, OUT, i_it);
      equal_exprt equality(lhs, rhs);
      nodes[i_it].equalities.push_back(equality);
    }
  }

  #if 0
  // now build formulas for assumptions and assertions
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_assume())
    {
    }
    else if(i_it->is_assert())
    {
    }
  }

  // now build formulas for guards
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_goto())
    {
      nodet &node=nodes[i_it];
  
      // changes the guard
      nodes.push_back(nodet());
      nodet &n=nodes.back();
      n.guard=rename(guard);
    
      // order matters here, RHS is done before LHS
      n.equality.rhs()=rename(and_exprt(guard, i_it->guard));
      n.equality.lhs()=assign(guard);
    }
  }
  #endif
}

/*******************************************************************\

Function: function_SSAt::guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt function_SSAt::guard()
{
  return symbol_exprt("ssa::$guard", bool_typet());
}

/*******************************************************************\

Function: function_SSAt::rename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt function_SSAt::rename(const exprt &expr, kindt kind, locationt loc)
{
  if(expr.id()==ID_symbol)
    return name(to_symbol_expr(expr), kind, loc);
  else if(expr.id()==ID_address_of)
  {
    return expr;
  }
  else
  {
    exprt tmp=expr; // copy
    Forall_operands(it, tmp)
      *it=rename(*it, kind, loc);
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
  locationt loc)
{
  symbol_exprt new_symbol_expr=symbol; // copy
  const irep_idt &old_id=symbol.get_identifier();
  unsigned cnt=loc->location_number;
  irep_idt new_id=id2string(old_id)+"#"+
                  (kind==IN?"I":"O")+
                  i2string(cnt)+suffix;
  new_symbol_expr.set_identifier(new_id);
  return new_symbol_expr;
}

/*******************************************************************\

Function: function_SSAt::assign

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

Function: function_SSAt::collect_objects

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::collect_objects(const exprt &src)
{
  forall_operands(it, src)
    collect_objects(*it);
  
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
    collect_objects(it->guard);
    collect_objects(it->code);
  }
}

/*******************************************************************\

Function: function_SSAt::build_incoming

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::build_incoming()
{
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_goto())
    {
      nodes[i_it->get_target()].incoming.insert(i_it);
      
      if(!i_it->guard.is_true())
      {
        locationt next=i_it;
        next++;
        nodes[next].incoming.insert(i_it);
      }
    }
    else if(i_it->is_return())
    {
      // no successors
    }
    else if(i_it->is_throw())
    {
      // no successors
    }
    else
    {
      // target is next instruction
      locationt next=i_it;
      next++;
      nodes[next].incoming.insert(i_it);
    }
  }

  // now build equalities for incoming data-flow
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    const std::set<locationt> &incoming=nodes[i_it].incoming;
    
    if(incoming.empty()) continue;
    
    for(objectst::const_iterator
        o_it=objects.begin(); o_it!=objects.end(); o_it++)
    {
      exprt rhs=nil_exprt();

      // build phi-node    
      for(std::set<locationt>::const_iterator
          incoming_it=incoming.begin();
          incoming_it!=incoming.end();
          incoming_it++)
      {
        exprt incoming_value=name(*o_it, OUT, *incoming_it);

        if(rhs.is_nil()) // first
          rhs=incoming_value;
        else
        {
          rhs=if_exprt(name(guard(), OUT, *incoming_it), incoming_value, rhs);
        }
      }

      symbol_exprt lhs=name(*o_it, IN, i_it);
      equal_exprt equality(lhs, rhs);
      nodes[i_it].equalities.push_back(equality);
    }
  }
}

/*******************************************************************\

Function: function_SSAt::get_exprs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::get_exprs(const exprt &src, std::set<exprt> &dest)
{
  if(dest.insert(src).second)
  {
    forall_operands(it, src)
      get_exprs(*it, dest);
  }
}

/*******************************************************************\

Function: function_SSAt::optimize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::optimize()
{
  union_find<exprt> equal;
  std::set<exprt> exprs;
  
  for(nodest::iterator n_it=nodes.begin();
      n_it!=nodes.end();
      n_it++)
  {
    nodet &node=n_it->second;
    for(nodet::equalitiest::const_iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      equal.make_union(e_it->lhs(), e_it->rhs());
      get_exprs(e_it->lhs(), exprs);
      get_exprs(e_it->rhs(), exprs);
    }
  }
  
  // get a number for all expressions
  for(std::set<exprt>::const_iterator
      e_it=exprs.begin(); e_it!=exprs.end(); e_it++)
    equal.number(*e_it);
  
  // iterate until saturation
  while(true)
  {
    bool progress=false;
    
    for(std::set<exprt>::const_iterator
        e_it=exprs.begin(); e_it!=exprs.end(); e_it++)
    {
      if(e_it->id()==ID_if)
      {
        const if_exprt &if_expr=to_if_expr(*e_it);
        const exprt &t=if_expr.true_case();
        const exprt &f=if_expr.false_case();

        if(equal.same_set(t, f) && !equal.same_set(*e_it, t))
        {
          equal.make_union(*e_it, t);
          progress=true;
        }
      }
    }
    
    if(!progress) break;
  }
  
  // now we know what's equal; use to eliminate constraints
  for(nodest::iterator n_it=nodes.begin();
      n_it!=nodes.end();
      n_it++)
  {
    nodet &node=n_it->second;
    for(nodet::equalitiest::const_iterator
        e_it=node.equalities.begin();
        e_it!=node.equalities.end();
        e_it++)
    {
      if(e_it->rhs().id()==ID_if)
      {
        
      }
    }
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
  //exprt guard;

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    #if 0
    if(guard!=n_it->guard)
    {
      guard=n_it->guard;
      out << std::endl;
      out << "[" << from_expr(ns, "", guard) << "]" << std::endl;
    }
    #endif
    
    const nodest::const_iterator n_it=nodes.find(i_it);
    if(n_it==nodes.end()) continue;

    out << "*** " << i_it->location << std::endl;
    output(n_it->second, out);
    out << std::endl;
  }
}

/*******************************************************************\

Function: function_SSAt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_SSAt::output(const nodet &node, std::ostream &out) const
{
  for(nodet::equalitiest::const_iterator
      e_it=node.equalities.begin();
      e_it!=node.equalities.end();
      e_it++)
    out << from_expr(ns, "", *e_it) << std::endl;
}

