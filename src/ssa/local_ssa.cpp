/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/i2string.h>
#include <util/prefix.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/byte_operators.h>

#include <goto-symex/adjust_float_expressions.h>

#include <langapi/language_util.h>

#include "local_ssa.h"
#include "malloc_ssa.h"
#include "address_canonizer.h"
#include "ssa_aliasing.h"

/*******************************************************************\

Function: local_SSAt::build_SSA

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::build_SSA()
{
  // perform SSA data-flow analysis
  ssa_analysis(goto_function, ns);
  
  // now build phi-nodes
  forall_goto_program_instructions(i_it, goto_function.body)
    build_phi_nodes(i_it);
  
  // now build transfer functions
  forall_goto_program_instructions(i_it, goto_function.body)
    build_transfer(i_it);

  // now build branching conditions
  forall_goto_program_instructions(i_it, goto_function.body)
    build_cond(i_it);

  // now build guards
  forall_goto_program_instructions(i_it, goto_function.body)
    build_guard(i_it);

  // entry and exit variables
  get_entry_exit_vars();

}

/*******************************************************************\

Function: local_SSAt::get_entry_exit_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::get_entry_exit_vars()
{
  //TODO: functions with side effects

  //get parameters
  const code_typet::argumentst &argument_types=goto_function.type.arguments();
  for(code_typet::argumentst::const_iterator
      it=argument_types.begin(); it!=argument_types.end(); it++)
  {
    const code_typet::argumentt &argument=*it;
    const irep_idt &identifier=argument.get_identifier();
    const symbolt &symbol=ns.lookup(identifier);
    params.push_back(symbol.symbol_expr());
  }

  //get globals in 
  goto_programt::const_targett first = goto_function.body.instructions.begin();
  get_globals(first,globals_in,false); //filters out #return_value

  //get globals out (includes return value)
  goto_programt::const_targett last = goto_function.body.instructions.end(); last--;
  get_globals(last,globals_out);
}

/*******************************************************************\

Function: local_SSAt::get_globals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::get_globals(locationt loc, std::set<symbol_exprt> &globals, bool returns)
{
  const ssa_domaint &ssa_domain=ssa_analysis[loc];
  for(ssa_domaint::def_mapt::const_iterator d_it = ssa_domain.def_map.begin();
      d_it != ssa_domain.def_map.end(); d_it++)
  {
    const symbolt *symbol;
    if(ns.lookup(d_it->first,symbol)) continue;         
    if(has_static_lifetime(symbol->symbol_expr()))
    {
      if(!returns && id2string(symbol->name).find("#return_value")!=std::string::npos) continue;
      const ssa_objectt ssa_object(symbol->symbol_expr(),ns);
      globals.insert(name(ssa_object,d_it->second.def));
    }
  }
}   

/*******************************************************************\

Function: local_SSAt::edge_guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt local_SSAt::edge_guard(locationt from, locationt to) const
{
  if(from->is_goto())
  {
    // big question: taken or not taken?
    if(to==from->get_target())
      return and_exprt(guard_symbol(from), cond_symbol(from));
    else
      return and_exprt(guard_symbol(from), not_exprt(cond_symbol(from)));
  }
  else if(from->is_assume())
  {
    return and_exprt(guard_symbol(from), cond_symbol(from));
  }
  else
    return guard_symbol(from);
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
      o_it=ssa_objects.objects.begin();
      o_it!=ssa_objects.objects.end(); o_it++)
  {
    // phi-node here?
    ssa_domaint::phi_nodest::const_iterator p_it=
      phi_nodes.find(o_it->get_identifier());
          
    if(p_it==phi_nodes.end()) continue; // none
    
    // Yes. Get the source -> def map.
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
          exprt incoming_guard=edge_guard(incoming_it->first, loc);

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
  /*
  else if(loc->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(loc->code);
      
    if(code_function_call.lhs().is_not_nil())
    {
      // generate a symbol for rhs
      irep_idt identifier="ssa::return_value"+i2string(loc->location_number);
      symbol_exprt rhs(identifier, code_function_call.lhs().type());
      
      assign_rec(code_function_call.lhs(), rhs, loc);
    }
  }
*/

  else if(loc->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(loc->code);

    exprt lhs = code_function_call.lhs();

    function_application_exprt ssa_rhs;
    ssa_rhs.function() = code_function_call.function();
    ssa_rhs.type() = code_function_call.lhs().type();
    ssa_rhs.arguments() = code_function_call.arguments(); 

    assign_rec(lhs, ssa_rhs, loc);
  }
}
  
/*******************************************************************\

Function: local_SSAt::build_cond

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::build_cond(locationt loc)
{
  // anything to be built?
  if(!loc->is_goto() &&
     !loc->is_assume()) return;
  
  // produce a symbol for the renamed branching condition
  equal_exprt equality(cond_symbol(loc), read_rhs(loc->guard, loc));
  nodes[loc].equalities.push_back(equality);
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
    
    exprt source;
    
    // might be backwards branch taken edge
    if(edge.is_branch_taken() &&
       edge.from->is_backwards_goto())
    {
      // The loop selector indicates whether the path comes from
      // above (entering the loop) or below (iterating).
      // By convention, we use the loop select symbol for the location
      // of the backwards goto.
      symbol_exprt loop_select=
        name(guard_symbol(), LOOP_SELECT, edge.from);

      #if 1
      source=false_exprt();
      #else
      // TODO: need constraing for edge.cond
      source=loop_select;
      #endif
    }
    else
    {
      // the other cases are basically similar
      
      symbol_exprt gs=name(guard_symbol(), OUT, edge.guard_source);

      exprt cond;
      
      if(edge.is_branch_taken() ||
         edge.is_assume() ||
         edge.is_function_call())
        cond=cond_symbol(edge.from);
      else if(edge.is_branch_not_taken())
        cond=boolean_negate(cond_symbol(edge.from));
      else if(edge.is_successor())
        cond=true_exprt();
      else
        assert(false);

      source=and_exprt(gs, cond);
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

Function: local_SSAt::cond_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ssa_objectt local_SSAt::cond_symbol() const
{
  return ssa_objectt(symbol_exprt("ssa::$cond", bool_typet()), ns);
}

/*******************************************************************\

Function: local_SSAt::guard_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ssa_objectt local_SSAt::guard_symbol() const
{
  return ssa_objectt(symbol_exprt("ssa::$guard", bool_typet()), ns);
}


/*******************************************************************\

Function: local_SSAt::read_rhs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt local_SSAt::read_rhs(
  const ssa_objectt &object,
  locationt loc) const
{
  const irep_idt &identifier=object.get_identifier();
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
  ssa_objectt object(expr, ns);

  // is this an object we track?
  if(ssa_objects.objects.find(object)!=
     ssa_objects.objects.end())
  {
    // yes, it is
    if(assignments.assigns(loc, object))
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
  const ssa_objectt &object,
  locationt loc) const
{
  // This reads:
  // * LOOP_BACK if there is a LOOP node at 'loc' for symbol
  // * OUT otherwise

  const irep_idt &identifier=object.get_identifier();
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
  exprt tmp=expr;
  adjust_float_expressions(tmp, ns);
  unsigned counter=0;
  replace_side_effects_rec(tmp, loc, counter);
  
  exprt result=read_rhs_rec(tmp, loc);
  
  return result;
}

/*******************************************************************\

Function: local_SSAt::read_rhs_address_of_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt local_SSAt::read_rhs_address_of_rec(
  const exprt &expr,
  locationt loc) const
{
  if(expr.id()==ID_dereference)
  {
    // We 'read' the pointer only, the dereferencing expression stays.
    dereference_exprt tmp=to_dereference_expr(expr);
    tmp.pointer()=read_rhs_rec(tmp.pointer(), loc);
    return tmp;
  }
  else if(expr.id()==ID_member)
  {
    member_exprt tmp=to_member_expr(expr);
    tmp.struct_op()=read_rhs_address_of_rec(tmp.struct_op(), loc);
    return tmp;
  }
  else if(expr.id()==ID_index)
  {
    index_exprt tmp=to_index_expr(expr);
    tmp.array()=read_rhs_address_of_rec(tmp.array(), loc);
    tmp.index()=read_rhs_rec(tmp.index(), loc);
    return tmp;
  }
  else if(expr.id()==ID_if)
  {
    if_exprt tmp=to_if_expr(expr);
    tmp.cond()=read_rhs_rec(tmp.cond(), loc);
    tmp.true_case()=read_rhs_address_of_rec(tmp.true_case(), loc);
    tmp.false_case()=read_rhs_address_of_rec(tmp.false_case(), loc);
    return tmp;
  }
  else
    return expr;
}

/*******************************************************************\

Function: local_SSAt::read_rhs_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt local_SSAt::read_rhs_rec(const exprt &expr, locationt loc) const
{
  if(is_deref_struct_member(expr, ns))
  {
    // Stuff like (*ptr).m1.m2 or simply *ptr.
    // This might alias with whatnot.

    // We use the identifier produced by
    // local_SSAt::replace_side_effects_rec
    exprt result=symbol_exprt(expr.get(ID_C_identifier), expr.type());

    // case split for aliasing
    for(objectst::const_iterator
        o_it=ssa_objects.objects.begin();
        o_it!=ssa_objects.objects.end(); o_it++)
    {
      if(ssa_may_alias(expr, o_it->get_expr(), ns))
      {
        exprt guard=ssa_alias_guard(expr, o_it->get_expr(), ns);
        exprt value=ssa_alias_value(expr, read_rhs(*o_it, loc), ns);
        guard=read_rhs_rec(guard, loc);
        value=read_rhs_rec(value, loc);

        result=if_exprt(guard, value, result);
      }
    }
    
    // may alias literals
    for(ssa_objectst::literalst::const_iterator
        o_it=ssa_objects.literals.begin();
        o_it!=ssa_objects.literals.end(); o_it++)
    {
      if(ssa_may_alias(expr, *o_it, ns))
      {
        exprt guard=ssa_alias_guard(expr, *o_it, ns);
        exprt value=ssa_alias_value(expr, read_rhs(*o_it, loc), ns);
        guard=read_rhs_rec(guard, loc);
        value=read_rhs_rec(value, loc);

        result=if_exprt(guard, value, result);
      }
    }
    
    return result;
  }
  else if(expr.id()==ID_sideeffect)
  {
    throw "unexpected side effect in read_rhs_rec";
  }
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt tmp=to_address_of_expr(expr);
    tmp.object()=read_rhs_address_of_rec(tmp.object(), loc);
    return address_canonizer(tmp, ns);
  }
  else if(expr.id()==ID_dereference)
  {
    // caught by case above
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    return index_exprt(read_rhs(index_expr.array(), loc),
                       read_rhs(index_expr.index(), loc),
                       expr.type());
  }
  
  ssa_objectt object(expr, ns);
  
  // is it an object identifier?
  
  if(!object)
  {
    exprt tmp=expr; // copy
    Forall_operands(it, tmp)
      *it=read_rhs(*it, loc);
    return tmp;
  }
  
  // Argument is a struct-typed ssa object?
  // May need to split up into members.
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_struct)
  {
    // build struct constructor
    struct_exprt result(expr.type());
  
    const struct_typet &struct_type=to_struct_type(type);
    const struct_typet::componentst &components=struct_type.components();
  
    result.operands().resize(components.size());
  
    for(struct_typet::componentst::const_iterator
        it=components.begin();
        it!=components.end();
        it++)
    {
      result.operands()[it-components.begin()]=
        read_rhs(member_exprt(expr, it->get_name(), it->type()), loc);
    }
  
    return result;
  }

  // is this an object we track?
  if(ssa_objects.objects.find(object)!=
     ssa_objects.objects.end())
  {
    return read_rhs(object, loc);
  }
  else
  {
    return name_input(object);
  }
}

/*******************************************************************\

Function: local_SSAt::replace_side_effects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_SSAt::replace_side_effects_rec(
  exprt &expr, locationt loc, unsigned &counter) const
{
  Forall_operands(it, expr)
    replace_side_effects_rec(*it, loc, counter);

  if(expr.id()==ID_sideeffect)
  {
    const side_effect_exprt &side_effect_expr=
      to_side_effect_expr(expr);
    const irep_idt statement=side_effect_expr.get_statement();

    if(statement==ID_nondet)
    {
      // turn into nondet_symbol
      exprt nondet_symbol(ID_nondet_symbol, expr.type());
      counter++;
      const irep_idt identifier=
        "ssa::nondet"+
        i2string(loc->location_number)+
        "."+i2string(counter)+suffix;
      nondet_symbol.set(ID_identifier, identifier);
      
      expr.swap(nondet_symbol);
    }
    else if(statement==ID_malloc)
    {
      counter++;
      std::string tmp_suffix=
        i2string(loc->location_number)+
        "."+i2string(counter)+suffix;
      expr=malloc_ssa(side_effect_expr, tmp_suffix, ns);
    }
    else
      throw "unexpected side effect: "+id2string(statement);
  }
  else if(is_deref_struct_member(expr, ns))
  {
    // We generate a symbol identifier in case dereferencing turns
    // out to need one.
    counter++;
    const irep_idt identifier=
      "ssa::deref"+
      i2string(loc->location_number)+
      "."+i2string(counter)+suffix;
    expr.set(ID_C_identifier, identifier);
  }
}

/*******************************************************************\

Function: local_SSAt::name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt local_SSAt::name(
  const ssa_objectt &object,
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
  const ssa_objectt &object,
  const ssa_domaint::deft &def) const
{
  if(def.is_input())
    return name_input(object);
  else if(def.is_phi())
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

symbol_exprt local_SSAt::name_input(const ssa_objectt &object) const
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
  bool flag_symbol=is_symbol_struct_member(lhs, ns);
  bool flag_deref=is_symbol_or_deref_struct_member(lhs, ns);

  const typet &type=ns.follow(lhs.type());
  
  if(flag_symbol || flag_deref || lhs.id()==ID_nil)
  {
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

      return;
    }

    ssa_objectt lhs_object(lhs, ns);
    
    exprt rhs_read=read_rhs(rhs, loc);

    const std::set<ssa_objectt> &assigned=
      assignments.get(loc);

    for(std::set<ssa_objectt>::const_iterator
        a_it=assigned.begin();
        a_it!=assigned.end();
        a_it++)
    {
      const symbol_exprt ssa_symbol=name(*a_it, OUT, loc);
      exprt ssa_rhs;
      
      if(lhs_object==*a_it)
      {
        ssa_rhs=rhs_read;
      }
      else if(lhs.id()==ID_dereference) // might alias stuff
      {
        const dereference_exprt &dereference_expr=
          to_dereference_expr(lhs);
      
        if(!ssa_may_alias(dereference_expr, a_it->get_expr(), ns))
          continue;
          
        exprt guard=ssa_alias_guard(dereference_expr, a_it->get_expr(), ns);
        exprt value=ssa_alias_value(dereference_expr, read_rhs(*a_it, loc), ns);
        
        exprt final_rhs=nil_exprt();
        
        // read the value and the rhs
        value=read_rhs(value, loc);
        
        // merge rhs into value
        if(value.id()==ID_symbol)
          final_rhs=rhs_read;
        else if(value.id()==ID_byte_extract_little_endian)
          final_rhs=byte_update_little_endian_exprt(
                          value.op0(), value.op1(), rhs_read);
        else if(value.id()==ID_byte_extract_big_endian)
          final_rhs=byte_update_big_endian_exprt(
                          value.op0(), value.op1(), rhs_read);
        
        if(final_rhs.is_nil())
          ssa_rhs=read_rhs(*a_it, loc);
        else
          ssa_rhs=if_exprt(
            read_rhs(guard, loc),
            final_rhs, // read_rhs done above
            read_rhs(*a_it, loc));
      }
      else if(lhs.id()==ID_nil) // functions without return value
      {
        irep_idt identifier="ssa::dummy"+i2string(loc->location_number);
        equal_exprt equality(symbol_exprt(identifier, bool_typet()), rhs_read);     	
        nodes[loc].equalities.push_back(equality);
        break;
      }
      else
        continue;
      
      equal_exprt equality(ssa_symbol, ssa_rhs);
      nodes[loc].equalities.push_back(equality);
    }
  }
  else if(lhs.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(lhs);
    exprt new_rhs=with_exprt(index_expr.array(), index_expr.index(), rhs);
    assign_rec(index_expr.array(), new_rhs, loc);
  }
  else if(lhs.id()==ID_member)
  {
    // These are non-flattened struct or union members.
    const member_exprt &member_expr=to_member_expr(lhs);
    const exprt &compound=member_expr.struct_op();
    const typet &compound_type=ns.follow(compound.type());

    if(compound_type.id()==ID_union)
    {
      union_exprt new_rhs(member_expr.get_component_name(), rhs, compound.type());
      assign_rec(member_expr.struct_op(), new_rhs, loc);
    }
    else if(compound_type.id()==ID_struct)
    {
      exprt member_name(ID_member_name);
      member_name.set(ID_component_name, member_expr.get_component_name());
      with_exprt new_rhs(compound, member_name, rhs);
      assign_rec(compound, new_rhs, loc);
    }
  }
  else if(lhs.id()==ID_complex_real)
  {
    assert(lhs.operands().size()==1);
    const exprt &op=lhs.op0();
    const complex_typet &complex_type=to_complex_type(op.type());
    exprt imag_op=unary_exprt(ID_complex_imag, op, complex_type.subtype());
    complex_exprt new_rhs(rhs, imag_op, complex_type);
    assign_rec(op, new_rhs, loc);
  }
  else if(lhs.id()==ID_complex_imag)
  {
    assert(lhs.operands().size()==1);
    const exprt &op=lhs.op0();
    const complex_typet &complex_type=to_complex_type(op.type());
    exprt real_op=unary_exprt(ID_complex_real, op, complex_type.subtype());
    complex_exprt new_rhs(real_op, rhs, complex_type);
    assign_rec(op, new_rhs, loc);
  }
  else
    throw "UNKNOWN LHS: "+lhs.id_string();
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
    out << "(E) " << from_expr(ns, "", *e_it) << "\n";

  for(constraintst::const_iterator
      e_it=constraints.begin();
      e_it!=constraints.end();
      e_it++)
    out << "(C) " << from_expr(ns, "", *e_it) << "\n";

}

/*******************************************************************\

Function: local_SSAt::has_static_lifetime

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool local_SSAt::has_static_lifetime(const ssa_objectt &object) const
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
    const symbolt *s;
    if(ns.lookup(to_symbol_expr(src).get_identifier(),s)) return false;
    return s->is_static_lifetime;
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

/*******************************************************************\

Function: local_SSAt::operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret & operator << (
  decision_proceduret &dest,
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
      dest << *e_it;
    }

    for(local_SSAt::nodet::constraintst::const_iterator
        c_it=n_it->second.constraints.begin();
        c_it!=n_it->second.constraints.end();
        c_it++)
    {
      dest << *c_it;
    }
  }
  
  return dest;
}

