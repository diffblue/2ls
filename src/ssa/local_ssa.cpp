/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/i2string.h>
#include <util/prefix.h>
#include <util/expr_util.h>
#include <util/decision_procedure.h>
#include <util/byte_operators.h>

#include <goto-symex/adjust_float_expressions.h>

#include "local_ssa.h"
#include "ssa_dereference.h"
#include "address_canonizer.h"

void local_SSAt::build_SSA()
{
  // perform SSA data-flow analysis
  ssa_analysis(goto_function, ns);

  forall_goto_program_instructions(i_it, goto_function.body)
  {
    nodest::iterator loophead_node=nodes.end();
    if(i_it->is_backwards_goto())
    {
      loophead_node=find_node(i_it->get_target());
    }
    nodes.push_back(nodet(i_it, loophead_node));

    build_transfer(i_it);
    build_phi_nodes(i_it);
    build_cond(i_it);
    build_guard(i_it);
    build_assertions(i_it);
    build_function_call(i_it);
//    build_unknown_objs(i_it);
    collect_record_frees(i_it);
  }

  // collect custom templates in loop heads
  collect_custom_templates();

  // entry and exit variables
  get_entry_exit_vars();
}

void local_SSAt::get_entry_exit_vars()
{
  // get parameters
  const code_typet::parameterst &parameter_types=
    goto_function.type.parameters();
  for(code_typet::parameterst::const_iterator
        it=parameter_types.begin(); it!=parameter_types.end(); it++)
  {
    const code_typet::parametert &parameter=*it;
    const irep_idt &identifier=parameter.get_identifier();

    const symbolt *symbol;
    if(ns.lookup(identifier, symbol))
      continue;

    params.push_back(symbol->symbol_expr());
  }

  // get globals in
  goto_programt::const_targett first=goto_function.body.instructions.begin();
  get_globals(first, globals_in, true, false); // filters out #return_value

  // get globals out (includes return value)
  goto_programt::const_targett
    last=goto_function.body.instructions.end(); last--;
  get_globals(last, globals_out, true, true, last->function);
}

void local_SSAt::get_globals(
  locationt loc,
  std::set<symbol_exprt> &globals,
  bool rhs_value,
  bool with_returns,
  const irep_idt &returns_for_function) const
{
  {
    const std::set<ssa_objectt> &ssa_globals=assignments.ssa_objects.globals;
    for(std::set<ssa_objectt>::const_iterator it=ssa_globals.begin();
        it!=ssa_globals.end(); it++)
    {
#if 0
      std::cout << "global: "
                << from_expr(ns, "", read_lhs(it->get_expr(), loc))
                << std::endl;
#endif
      if(!with_returns && !is_pointed(it->get_expr()) &&
         id2string(it->get_identifier()).find("#return_value")!=
         std::string::npos)
        continue;

      // filter out return values of other functions
      if(with_returns && returns_for_function!="" &&
        id2string(it->get_identifier()).find("#return_value")==
        id2string(it->get_identifier()).size()-
        std::string("#return_value").size() &&
        id2string(it->get_identifier()).find(
          id2string(returns_for_function)+"#return_value")==std::string::npos)
        continue;

      const exprt &root_obj=it->get_root_object();
      if(is_ptr_object(root_obj))
      {
        const symbolt *symbol;
        irep_idt ptr_obj_id=root_obj.get(ID_ptr_object);
        if(ns.lookup(ptr_obj_id, symbol))
          continue;
      }

      if(rhs_value)
      {
        ssa_objectt object(it->get_expr(), ns);
        const exprt &expr=read_rhs(object, loc);
        globals.insert(to_symbol_expr(expr));
      }
      else
      {
        const exprt &expr=read_lhs(it->get_expr(), loc);
        globals.insert(to_symbol_expr(expr));
      }
    }
  }
}


void local_SSAt::collect_custom_templates()
{
  for(local_SSAt::nodest::iterator n_it=nodes.begin();
      n_it!=nodes.end(); n_it++)
  {
    if(n_it->loophead!=nodes.end()) // we've found a loop
    {
      // search for templates in the loop
      for(local_SSAt::nodest::iterator nn_it=n_it->loophead;
          nn_it!=n_it; nn_it++)
      {
        if(nn_it->templates.empty())
          continue;

        n_it->loophead->templates.insert(
          n_it->loophead->templates.end(),
          nn_it->templates.begin(),
          nn_it->templates.end());
        nn_it->templates.clear();
      }
    }
  }
}

local_SSAt::nodest::iterator local_SSAt::find_node(locationt loc)
{
  nodest::iterator n_it=nodes.begin();
  for(; n_it!=nodes.end(); n_it++)
  {
    if(n_it->location==loc)
      break;
  }
  return n_it;
}

local_SSAt::nodest::const_iterator local_SSAt::find_node(locationt loc) const
{
  nodest::const_iterator n_it=nodes.begin();
  for(; n_it!=nodes.end(); n_it++)
  {
    if(n_it->location==loc)
      break;
  }
  return n_it;
}

void local_SSAt::find_nodes(
  locationt loc,
  std::list<nodest::const_iterator> &_nodes) const
{
  nodest::const_iterator n_it=nodes.begin();
  for(; n_it!=nodes.end(); n_it++)
  {
    if(n_it->location==loc)
      _nodes.push_back(n_it);
  }
}

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

void local_SSAt::build_phi_nodes(locationt loc)
{
  const ssa_domaint::phi_nodest &phi_nodes=ssa_analysis[loc].phi_nodes;
  nodet &node=*(--nodes.end());

  for(objectst::const_iterator
        o_it=ssa_objects.objects.begin();
      o_it!=ssa_objects.objects.end(); ++o_it)
  {
    // phi-node for this object here?
    ssa_domaint::phi_nodest::const_iterator p_it=
      phi_nodes.find(o_it->get_identifier());

    if(p_it==phi_nodes.end()) // none
      continue;

#ifdef DEBUG
    std::cout << "PHI " << o_it->get_identifier() << "\n";
#endif

    // ignore custom template variables
    if(id2string(o_it->get_identifier()).
       find(TEMPLATE_PREFIX)!=std::string::npos) continue;

    // Yes. Get the source -> def map.
    const ssa_domaint::loc_def_mapt &incoming=p_it->second;

    exprt rhs=nil_exprt();

    // We distinguish forwards- from backwards-edges,
    // and do forwards-edges first, which gives them
    // _lower_ priority in the ITE. Inputs are always
    // forward edges.

    for(ssa_domaint::loc_def_mapt::const_iterator
          incoming_it=incoming.begin();
        incoming_it!=incoming.end();
        incoming_it++)
      if(incoming_it->second.is_input() ||
         incoming_it->first<loc->location_number)
      {
        // it's a forward edge
        exprt incoming_value=name(*o_it, incoming_it->second);
        // TODO: investigate: here is some nondeterminism
        //  whether g2 (=g1&c1 (maybe)) or (g1&c1) is used,
        //  not sure whether this has consequences
        //  (further than the SSA looking different each time you generate it)
        exprt incoming_guard=edge_guard(get_location(incoming_it->first), loc);

        if(rhs.is_nil()) // first
          rhs=incoming_value;
        else
          rhs=if_exprt(incoming_guard, incoming_value, rhs);
      }

    // now do backwards

    for(ssa_domaint::loc_def_mapt::const_iterator
          incoming_it=incoming.begin();
        incoming_it!=incoming.end();
        incoming_it++)
      if(!incoming_it->second.is_input() &&
         incoming_it->first>=loc->location_number)
      {
        // it's a backwards edge
        const locationt &iloc=get_location(incoming_it->first);
        exprt incoming_value=name(*o_it, LOOP_BACK, iloc);
        exprt incoming_select=name(guard_symbol(), LOOP_SELECT, iloc);
        loop_guards.insert(
          std::make_pair(
            to_symbol_expr(incoming_select),
            to_symbol_expr(guard_symbol(loc))));

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

exprt local_SSAt::dereference(const exprt &src, locationt loc) const
{
  const ssa_value_domaint &ssa_value_domain=ssa_value_ai[loc];
  const std::string nondet_prefix="deref#"+i2string(loc->location_number);
  return ::dereference(src, ssa_value_domain, nondet_prefix, ns);
}

void local_SSAt::build_transfer(locationt loc)
{
  if(loc->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(loc->code);

    // template declarations
    if(code_assign.lhs().id()==ID_symbol &&
       id2string(code_assign.lhs().get(ID_identifier)).
       find("return_value_" TEMPLATE_NEWVAR)!=std::string::npos)
    {
      // propagate equalities through replace map
      exprt lhs=code_assign.lhs();
      template_newvars[lhs]=template_newvars[template_last_newvar];
      template_last_newvar=lhs;
      return;
    }
    if(code_assign.lhs().id()==ID_symbol &&
       id2string(code_assign.lhs().get(ID_identifier)).
       find(TEMPLATE_PREFIX)!=std::string::npos) return;
    if(code_assign.rhs().id()==ID_symbol &&
       id2string(code_assign.rhs().get(ID_identifier)).
       find(TEMPLATE_PREFIX)!=std::string::npos) return;

    // build allocation guards map
    collect_allocation_guards(code_assign, loc);

    exprt deref_lhs=dereference(code_assign.lhs(), loc);
    exprt deref_rhs=dereference(code_assign.rhs(), loc);

    if(deref_lhs.get_bool("#heap_access") || deref_rhs.get_bool("#heap_access"))
    {
      exprt symbolic_deref_lhs=symbolic_dereference(code_assign.lhs(), ns);
      const exprt rhs=concretise_symbolic_deref_rhs(code_assign.rhs(), ns, loc);

      if(deref_lhs.get_bool("#heap_access") &&
         has_symbolic_deref(symbolic_deref_lhs))
      {
        assign_rec(symbolic_deref_lhs, rhs, true_exprt(), loc);
        assign_rec(
          deref_lhs,
          symbolic_deref_lhs,
          true_exprt(),
          loc,
          true);
      }
      else
      {
        assign_rec(deref_lhs, rhs, true_exprt(), loc);
      }
    }
    else
      assign_rec(deref_lhs, deref_rhs, true_exprt(), loc);
  }
}

void local_SSAt::build_function_call(locationt loc)
{
  if(loc->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(loc->code);

    const exprt &lhs=code_function_call.lhs();

    if(lhs.is_not_nil())
    {
      exprt deref_lhs=dereference(lhs, loc);

      // generate a symbol for rhs
      irep_idt identifier="ssa::return_value"+i2string(loc->location_number);
      symbol_exprt rhs(identifier, code_function_call.lhs().type());

      assign_rec(deref_lhs, rhs, true_exprt(), loc);
    }

    nodest::iterator n_it=--nodes.end();

    // template declarations
    if(code_function_call.function().id()==ID_symbol &&
       has_prefix(
         TEMPLATE_DECL,
         id2string(code_function_call.function().get(ID_identifier))))
    {
      assert(code_function_call.arguments().size()==1);
      n_it->templates.push_back(code_function_call.arguments()[0]);

      // replace "new" vars
      replace_expr(template_newvars, n_it->templates.back());

#if 0
      std::cout << "found template declaration: "
                << from_expr(ns, "", code_function_call.arguments()[0])
                << std::endl;
#endif
      template_newvars.clear();
      return;
    }

    // turn function call into expression
    function_application_exprt f;
    f.function()=code_function_call.function();
    f.type()=code_function_call.lhs().type();
    f.arguments()=code_function_call.arguments();

    // access to "new" value in template declarations
    if(code_function_call.function().id()==ID_symbol &&
       has_prefix(
         TEMPLATE_NEWVAR,
         id2string(code_function_call.function().get(ID_identifier))))
    {
      assert(code_function_call.arguments().size()==1);
      template_last_newvar=f;
      template_newvars[template_last_newvar]=template_last_newvar;
      return;
    }

    assert(f.function().id()==ID_symbol); // no function pointers

    f=to_function_application_expr(read_rhs(f, loc));

    irep_idt fname=to_symbol_expr(f.function()).get_identifier();
    // add equalities for arguments
    unsigned i=0;
    for(exprt &a : f.arguments())
    {
      const std::string arg_name=
        id2string(fname)+"#arg"+i2string(i)+"#"+
          i2string(loc->location_number);
      symbol_exprt arg(arg_name, a.type());
      n_it->equalities.push_back(equal_exprt(a, arg));
      a=arg;
      ++i;
    }

    n_it->function_calls.push_back(to_function_application_expr(f));
  }
}

void local_SSAt::build_cond(locationt loc)
{
  // anything to be built?
  if(loc->is_goto() || loc->is_assume())
  {
    // produce a symbol for the renamed branching condition
    equal_exprt equality(cond_symbol(loc), read_rhs(loc->guard, loc));
    (--nodes.end())->equalities.push_back(equality);
  }
  else if(loc->is_function_call())
  {
    equal_exprt equality(cond_symbol(loc), true_exprt());
    (--nodes.end())->equalities.push_back(equality);
  }
}

void local_SSAt::build_guard(locationt loc)
{
  const guard_mapt::entryt &entry=guard_map[loc];

  // anything to be built?
  if(!entry.has_guard)
    return;

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

      source=false_exprt();
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
  (--nodes.end())->equalities.push_back(equality);
}

/// turns assertions into constraints
void local_SSAt::build_assertions(locationt loc)
{
  if(loc->is_assert())
  {
    exprt assert=loc->guard;
    if(assert.id()==ID_not && assert.op0().id()==ID_equal &&
       assert.op0().op1().id()==ID_pointer_object &&
       assert.op0().op1().op0().id()==ID_symbol)
    {
      std::string id=id2string(
        to_symbol_expr(assert.op0().op1().op0()).get_identifier());
      if(id.find("__CPROVER_deallocated")!=std::string::npos)
      {
        const exprt &dealloc_symbol=assert.op0().op1().op0();
        exprt::operandst d;
        for(auto &global : assignments.ssa_objects.globals)
        {
          if(global.get_expr().get_bool("#concrete"))
          {
            d.push_back(
              equal_exprt(
                dealloc_symbol,
                typecast_exprt(
                  address_of_exprt(global.symbol_expr()),
                  dealloc_symbol.type())));
          }
        }
        assert=implies_exprt(disjunction(d), assert);
      }
    }

    const exprt deref_rhs=dereference(assert, loc);
    collect_iterators_rhs(deref_rhs, loc);

    const exprt rhs=concretise_symbolic_deref_rhs(assert, ns, loc);
    exprt c=read_rhs(rhs, loc);
    exprt g=guard_symbol(loc);
    (--nodes.end())->assertions.push_back(implies_exprt(g, c));
  }
}

/// turns assertions into constraints
void local_SSAt::assertions_to_constraints()
{
  for(nodest::iterator
        n_it=nodes.begin();
      n_it!=nodes.end();
      n_it++)
  {
    n_it->constraints.insert(
      n_it->constraints.end(),
      n_it->assertions.begin(),
      n_it->assertions.end());
  }
}

ssa_objectt local_SSAt::cond_symbol() const
{
  return ssa_objectt(symbol_exprt("ssa::$cond", bool_typet()), ns);
}

ssa_objectt local_SSAt::guard_symbol() const
{
  return ssa_objectt(symbol_exprt("ssa::$guard", bool_typet()), ns);
}


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

exprt local_SSAt::read_lhs(
  const exprt &expr,
  locationt loc) const
{
  // dereference first
  exprt tmp1=dereference(expr, loc);

#ifdef DEBUG
  std::cout << "read_lhs tmp1: " << from_expr(ns, "", tmp1) << '\n';
#endif

  ssa_objectt object(tmp1, ns);

  // is this an object we track?
  if(ssa_objects.objects.find(object)!=
     ssa_objects.objects.end())
  {
#ifdef DEBUG
    std::cout << from_expr(ns, "", tmp1) << "is_object" << '\n';
#endif

    // yes, it is
    if(assignments.assigns(loc, object))
      return name(object, OUT, loc);
    else
      return read_rhs(object, loc);
  }
  else
    return read_rhs(tmp1, loc);
}

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
    const ssa_domaint::loc_def_mapt &incoming=p_it->second;

    for(const auto &incoming_it : incoming)
    {
      if(incoming_it.first>loc->location_number)
        has_phi=true;
    }
  }

  if(has_phi)
    return name(object, LOOP_BACK, loc);
  else
    return read_rhs(object, loc);
}

local_SSAt::locationt local_SSAt::get_def_loc(
  const symbol_exprt &expr,
  locationt loc) const
{
  ssa_objectt object(expr, ns);
  if(!object)
    assert(false);
  if(ssa_objects.objects.find(object)!=
     ssa_objects.objects.end())
  {
    const irep_idt &identifier=object.get_identifier();
    const ssa_domaint &ssa_domain=ssa_analysis[loc];

    ssa_domaint::def_mapt::const_iterator d_it=
      ssa_domain.def_map.find(identifier);

    if(d_it==ssa_domain.def_map.end()) // input
      return goto_function.body.instructions.begin();
    else
      return d_it->second.def.loc; // last definition
  }
  else // input
    return goto_function.body.instructions.begin();
}

exprt local_SSAt::read_rhs(const exprt &expr, locationt loc) const
{
  exprt tmp1=expr;
  adjust_float_expressions(tmp1, ns);

  unsigned counter=0;
  replace_side_effects_rec(tmp1, loc, counter);

#ifdef DEBUG
  std::cout << "read_rhs tmp1: " << from_expr(ns, "", tmp1) << '\n';
#endif

  exprt tmp2=dereference(tmp1, loc);

#ifdef DEBUG
  std::cout << "read_rhs tmp2: " << from_expr(ns, "", tmp2) << '\n';
#endif

  exprt result=read_rhs_rec(tmp2, loc);

#ifdef DEBUG
  std::cout << "read_rhs result: " << from_expr(ns, "", result) << '\n';
#endif

  return result;
}

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

exprt local_SSAt::read_rhs_rec(const exprt &expr, locationt loc) const
{
  if(expr.id()==ID_side_effect)
  {
    // ignore

    // throw "unexpected side effect in read_rhs_rec";
  }
  else if(expr.id()==ID_address_of)
  {
    address_of_exprt tmp=to_address_of_expr(expr);
    tmp.object()=read_rhs_address_of_rec(tmp.object(), loc);
    return address_canonizer(tmp, ns);
  }
  else if(expr.id()==ID_dereference)
  {
    throw "unexpected dereference in read_rhs_rec";
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    return index_exprt(
      read_rhs(index_expr.array(), loc),
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

#if 0
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
#endif

  // is this an object we track?
  if(ssa_objects.objects.find(object)!=
     ssa_objects.objects.end())
  {
    // If the last definition of an object is at its allocation, we can only use
    // the corresponding symbol if the object has truly been allocated
    // (allocation guard holds). Otherwise we need to use the last definition
    // before the allocation.
    auto def_it=ssa_analysis[loc].def_map.find(object.get_identifier());
    if(def_it!=ssa_analysis[loc].def_map.end() &&
       def_it->second.def.kind==ssa_domaint::deft::ALLOCATION)
    {
      locationt alloc_loc=def_it->second.def.loc;
      return if_exprt(
        read_rhs(def_it->second.def.guard, alloc_loc),
        read_rhs(object, loc),
        read_rhs(object, alloc_loc));
    }
    else
      return read_rhs(object, loc);
  }
  else
  {
    return name_input(object);
  }
}

void local_SSAt::replace_side_effects_rec(
  exprt &expr, locationt loc, unsigned &counter) const
{
  Forall_operands(it, expr)
    replace_side_effects_rec(*it, loc, counter);

  if(expr.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=
      to_side_effect_expr(expr);
    const irep_idt statement=side_effect_expr.get_statement();

    if(statement==ID_nondet)
    {
      // turn into nondet_symbol
      counter++;
      exprt s=nondet_symbol("ssa::nondet", expr.type(), loc, counter);
      expr.swap(s);
    }
    else if(statement==ID_malloc)
    {
      assert(false);
/*      counter++;
        std::string tmp_suffix=
        i2string(loc->location_number)+
        "."+i2string(counter)+suffix;
        expr=malloc_ssa(side_effect_expr, tmp_suffix, ns);*/
    }
    else
    {
      // throw "unexpected side effect: "+id2string(statement);
      // ignore
    }
  }
}

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
      kind==OBJECT_SELECT?"os":"")+
    i2string(cnt)+
    (kind==LOOP_SELECT?std::string(""):suffix);

#ifdef DEBUG
  std::cout << "name " << kind << ": " << new_id << '\n';
#endif

  new_symbol_expr.set_identifier(new_id);

  if(object.get_expr().source_location().is_not_nil())
    new_symbol_expr.add_source_location()=object.get_expr().source_location();

  copy_pointed_info(new_symbol_expr, object.get_expr());

  return new_symbol_expr;
}

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

symbol_exprt local_SSAt::name_input(const ssa_objectt &object) const
{
  symbol_exprt new_symbol_expr(object.get_expr().type()); // copy
  const irep_idt old_id=object.get_identifier();
  irep_idt new_id=id2string(old_id)+suffix; // +"#in"
  new_symbol_expr.set_identifier(new_id);

  if(object.get_expr().source_location().is_not_nil())
    new_symbol_expr.add_source_location()=object.get_expr().source_location();

  copy_pointed_info(new_symbol_expr, object.get_expr());

  return new_symbol_expr;
}

exprt local_SSAt::nondet_symbol(
  std::string prefix,
  const typet &type,
  locationt loc,
  unsigned counter) const
{
  exprt s(ID_nondet_symbol, type);
  const irep_idt identifier=
    prefix+
    i2string(loc->location_number)+
    "."+i2string(counter)+suffix;
  s.set(ID_identifier, identifier);
  return s;
}

void local_SSAt::assign_rec(
  const exprt &lhs,
  const exprt &rhs,
  const exprt &guard,
  locationt loc,
  bool fresh_rhs)
{
  const typet &type=ns.follow(lhs.type());

  if(is_symbol_struct_member(lhs, ns))
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
        assign_rec(new_lhs, new_rhs, guard, loc, fresh_rhs);
      }

      return;
    }

    ssa_objectt lhs_object(lhs, ns);

    const std::set<ssa_objectt> &assigned=
      assignments.get(loc);

    if(assigned.find(lhs_object)!=assigned.end())
    {
      collect_iterators_lhs(lhs_object, loc);
      collect_iterators_rhs(rhs, loc);

      exprt ssa_rhs=fresh_rhs ? name(ssa_objectt(rhs, ns), OUT, loc)
                              : read_rhs(rhs, loc);

      const symbol_exprt ssa_symbol=name(lhs_object, OUT, loc);

      equal_exprt equality(ssa_symbol, ssa_rhs);
      (--nodes.end())->equalities.push_back(equality);
    }
  }
  else if(lhs.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(lhs);
    exprt ssa_array=index_expr.array();
    exprt new_rhs=with_exprt(ssa_array, index_expr.index(), rhs);
    assign_rec(index_expr.array(), new_rhs, guard, loc, fresh_rhs);
  }
  else if(lhs.id()==ID_member)
  {
    // These are non-flattened struct or union members.
    const member_exprt &member_expr=to_member_expr(lhs);
    const exprt &compound=member_expr.struct_op();
    const typet &compound_type=ns.follow(compound.type());

    if(compound_type.id()==ID_union)
    {
      union_exprt new_rhs(
        member_expr.get_component_name(), rhs, compound.type());
      assign_rec(member_expr.struct_op(), new_rhs, guard, loc, fresh_rhs);
    }
    else if(compound_type.id()==ID_struct)
    {
      exprt member_name(ID_member_name);
      member_name.set(ID_component_name, member_expr.get_component_name());
      with_exprt new_rhs(compound, member_name, rhs);
      assign_rec(compound, new_rhs, guard, loc, fresh_rhs);
    }
  }
  else if(lhs.id()==ID_complex_real)
  {
    assert(lhs.operands().size()==1);
    const exprt &op=lhs.op0();
    const complex_typet &complex_type=to_complex_type(op.type());
    exprt imag_op=unary_exprt(ID_complex_imag, op, complex_type.subtype());
    complex_exprt new_rhs(rhs, imag_op, complex_type);
    assign_rec(op, new_rhs, guard, loc, fresh_rhs);
  }
  else if(lhs.id()==ID_complex_imag)
  {
    assert(lhs.operands().size()==1);
    const exprt &op=lhs.op0();
    const complex_typet &complex_type=to_complex_type(op.type());
    exprt real_op=unary_exprt(ID_complex_real, op, complex_type.subtype());
    complex_exprt new_rhs(real_op, rhs, complex_type);
    assign_rec(op, new_rhs, guard, loc, fresh_rhs);
  }
  else if(lhs.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(lhs);

    exprt::operandst other_cond_conj;
    if(if_expr.true_case().get_bool("#heap_access") &&
       if_expr.cond().id()==ID_equal)
    {
      const exprt heap_object=if_expr.true_case();
      const ssa_objectt ptr_object(to_equal_expr(if_expr.cond()).lhs(), ns);
      if(ptr_object)
      {
        const irep_idt ptr_id=ptr_object.get_identifier();
        const exprt cond=read_rhs(if_expr.cond(), loc);

        for(const dyn_obj_assignt &do_assign : dyn_obj_assigns[heap_object])
        {
          if(!alias_analysis[loc].aliases.same_set(
            ptr_id, do_assign.pointer_id))
          {
            other_cond_conj.push_back(do_assign.cond);
          }
        }

        dyn_obj_assigns[heap_object].emplace_back(ptr_id, cond);
      }
    }

    exprt cond=if_expr.cond();
    if(!other_cond_conj.empty())
    {
      const exprt other_cond=or_exprt(
        not_exprt(conjunction(other_cond_conj)),
        name(guard_symbol(), OBJECT_SELECT, loc));
      cond=and_exprt(cond, other_cond);
    }
    exprt orig_rhs=fresh_rhs ? name(ssa_objectt(rhs, ns), OUT, loc) : rhs;
    exprt new_rhs=if_exprt(cond, orig_rhs, if_expr.true_case());
    assign_rec(
      if_expr.true_case(),
      new_rhs,
      and_exprt(guard, if_expr.cond()),
      loc);

    assign_rec(
      if_expr.false_case(),
      rhs,
      and_exprt(guard, not_exprt(if_expr.cond())),
      loc,
      fresh_rhs);
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &byte_extract_expr=to_byte_extract_expr(lhs);

    exprt new_lhs=byte_extract_expr.op();

    exprt new_rhs=byte_extract_exprt(
      byte_extract_expr.id(), rhs, byte_extract_expr.offset(), new_lhs.type());

    assign_rec(new_lhs, new_rhs, guard, loc, fresh_rhs);
  }
  else
    throw "UNKNOWN LHS: "+lhs.id_string(); // NOLINT(*)
}

void local_SSAt::output(std::ostream &out) const
{
  for(nodest::const_iterator
        n_it=nodes.begin();
      n_it!=nodes.end(); n_it++)
  {
    if(n_it->empty())
      continue;
    n_it->output(out, ns);
    out << '\n';
  }
}

void local_SSAt::output_verbose(std::ostream &out) const
{
  for(nodest::const_iterator
        n_it=nodes.begin();
      n_it!=nodes.end(); n_it++)
  {
    if(n_it->empty())
      continue;
    out << "*** " << n_it->location->location_number
        << " " << n_it->location->source_location << "\n";
    n_it->output(out, ns);
    if(n_it->loophead!=nodes.end())
      out << "loop back to location "
          << n_it->loophead->location->location_number << "\n";
    if(!n_it->enabling_expr.is_true())
      out << "enabled if "
          << from_expr(ns, "", n_it->enabling_expr) << "\n";
    out << "\n";
  }
  out << "(enable) " << from_expr(ns, "", get_enabling_exprs()) << "\n\n";
}

void local_SSAt::nodet::output(
  std::ostream &out,
  const namespacet &ns) const
{
#if 0
  if(!marked)
    out << "(not marked)" << "\n";
#endif
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

  for(assertionst::const_iterator
        a_it=assertions.begin();
      a_it!=assertions.end();
      a_it++)
    out << "(A) " << from_expr(ns, "", *a_it) << "\n";

  for(function_callst::const_iterator
        f_it=function_calls.begin();
      f_it!=function_calls.end();
      f_it++)
    out << "(F) " << from_expr(ns, "", *f_it) << "\n";
}

bool local_SSAt::has_static_lifetime(const ssa_objectt &object) const
{
  return has_static_lifetime(object.get_expr());
}

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
    if(ns.lookup(to_symbol_expr(src).get_identifier(), s))
      return false;
    return s->is_static_lifetime;
  }
  else
    return false;
}

std::list<exprt> &operator<<(
  std::list<exprt> &dest,
  const local_SSAt &src)
{
#ifdef SLICING
  ssa_slicert ssa_slicer;
  ssa_slicer(dest, src);
#else
  for(local_SSAt::nodest::const_iterator n_it=src.nodes.begin();
      n_it!=src.nodes.end(); n_it++)
  {
    if(n_it->marked)
      continue;
    for(local_SSAt::nodet::equalitiest::const_iterator
          e_it=n_it->equalities.begin();
        e_it!=n_it->equalities.end();
        e_it++)
    {
      dest.push_back(*e_it);
    }

    for(local_SSAt::nodet::constraintst::const_iterator
          c_it=n_it->constraints.begin();
        c_it!=n_it->constraints.end();
        c_it++)
    {
      dest.push_back(*c_it);
    }
  }
#endif

  return dest;
}

decision_proceduret &operator<<(
  decision_proceduret &dest,
  const local_SSAt &src)
{
#ifdef SLICING
  std::list<exprt> tmp;
  tmp << src;
  for(std::list<exprt>::const_iterator it=tmp.begin();
      it!=tmp.end(); it++)
    dest << *it;
#else
  for(local_SSAt::nodest::const_iterator n_it=src.nodes.begin();
      n_it!=src.nodes.end(); n_it++)
  {
    if(n_it->marked)
      continue;
    for(local_SSAt::nodet::equalitiest::const_iterator
          e_it=n_it->equalities.begin();
        e_it!=n_it->equalities.end();
        e_it++)
    {
      dest << *e_it;
    }

    for(local_SSAt::nodet::constraintst::const_iterator
          c_it=n_it->constraints.begin();
        c_it!=n_it->constraints.end();
        c_it++)
    {
      dest << *c_it;
    }
  }
#endif
  return dest;
}

incremental_solvert &operator<<(
  incremental_solvert &dest,
  const local_SSAt &src)
{
#ifdef SLICING
  std::list<exprt> tmp;
  tmp << src;
  for(std::list<exprt>::const_iterator it=tmp.begin();
      it!=tmp.end(); it++)
    dest << *it;
#else
  for(local_SSAt::nodest::const_iterator n_it=src.nodes.begin();
      n_it!=src.nodes.end(); n_it++)
  {
    if(n_it->marked)
      continue;
    for(local_SSAt::nodet::equalitiest::const_iterator
          e_it=n_it->equalities.begin();
        e_it!=n_it->equalities.end();
        e_it++)
    {
      if(!n_it->enabling_expr.is_true())
        dest << implies_exprt(n_it->enabling_expr, *e_it);
      else
        dest << *e_it;

#if 0
      // freeze cond variables
      if(e_it->op0().id()==ID_symbol &&
         e_it->op0().type().id()==ID_bool)
      {
        const symbol_exprt &symbol=to_symbol_expr(e_it->op0());
        if(id2string(symbol.get_identifier()).find("ssa::$cond")!=
           std::string::npos)
        {
          dest.solver->set_frozen(dest.solver->convert(symbol));
        }
      }
#endif
    }

    for(local_SSAt::nodet::constraintst::const_iterator
          c_it=n_it->constraints.begin();
        c_it!=n_it->constraints.end();
        c_it++)
    {
      if(!n_it->enabling_expr.is_true())
        dest << implies_exprt(n_it->enabling_expr, *c_it);
      else
        dest << *c_it;
    }
  }
#endif
  return dest;
}

exprt local_SSAt::get_enabling_exprs() const
{
  exprt::operandst result;
  result.reserve(enabling_exprs.size());
  for(std::list<symbol_exprt>::const_iterator it=enabling_exprs.begin();
      it!=enabling_exprs.end(); ++it)
  {
    std::list<symbol_exprt>::const_iterator lh=it; ++lh;
    if(lh!=enabling_exprs.end())
      result.push_back(not_exprt(*it));
    else
      result.push_back(*it);
  }
  return conjunction(result);
}

bool local_SSAt::has_function_calls() const
{
  bool found=false;
  for(local_SSAt::nodest::const_iterator n_it=nodes.begin();
      n_it!=nodes.end(); n_it++)
  {
    if(!n_it->function_calls.empty())
    {
      found=true;
      break;
    }
  }
  return found;
}

/// If a location is malloc call, create "unknown object" for return type. This
/// is later used as a placeholder for invalid of unknown dereference of an
/// object of that type.
void local_SSAt::build_unknown_objs(locationt loc)
{
  if(loc->is_assign())
  {
    const code_assignt &code_assign=to_code_assign(loc->code);
    const exprt &rhs=code_assign.rhs();
    if(rhs.get_bool("#malloc_result"))
    {
      const exprt &malloc_res=
        rhs.id()==ID_typecast ? to_typecast_expr(rhs).op() : rhs;
      const exprt &addr_of_do=
        malloc_res.id()==ID_if ? to_if_expr(malloc_res).true_case()
                               : malloc_res;
      const exprt &dyn_obj=to_address_of_expr(addr_of_do).object();
      const typet &dyn_type=ns.follow(dyn_obj.type());

      std::string dyn_type_name=dyn_type.id_string();
      if(dyn_type.id()==ID_struct)
        dyn_type_name+="_"+id2string(to_struct_type(dyn_type).get_tag());
      irep_idt identifier="ssa::"+dyn_type_name+"_obj$unknown";

      symbol_exprt unknown_obj(identifier, dyn_obj.type());
      unknown_objs.insert(unknown_obj);
    }
  }
}

/// Create equality obj.component = &obj, which creates self-loop on "unknown"
/// objects.
exprt local_SSAt::unknown_obj_eq(
  const symbol_exprt &obj,
  const struct_typet::componentt &component) const
{
  const irep_idt identifier=
    id2string(obj.get_identifier())+"."+id2string(component.get_name());
  const symbol_exprt member(identifier, component.type());
  return equal_exprt(member, address_of_exprt(obj));
}

void local_SSAt::collect_iterators_rhs(const exprt &expr, locationt loc)
{
  if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);
    if(member.compound().get_bool(ID_iterator) &&
       member.compound().id()==ID_symbol)
    {
      new_iterator_access(to_member_expr(expr), loc, list_iteratort::IN_LOC);
    }
  }
  else
  {
    forall_operands(it, expr)
      collect_iterators_rhs(*it, loc);
  }
}

void local_SSAt::collect_iterators_lhs(
  const ssa_objectt &object,
  local_SSAt::locationt loc)
{
  if(is_iterator(object.get_root_object()) &&
     object.get_root_object().id()==ID_symbol)
  {
    assert(object.get_expr().id()==ID_member);
    new_iterator_access(
      to_member_expr(object.get_expr()),
      loc,
      loc->location_number);
  }
}

/// Create new iterator access
void local_SSAt::new_iterator_access(
  const member_exprt &expr,
  local_SSAt::locationt loc,
  unsigned inst_loc_number)
{
  assert(is_iterator(expr.compound()));

  const irep_idt pointer_id=expr.compound().get(ID_it_pointer);
  const symbolt &pointer_symbol=ns.lookup(pointer_id);
  exprt pointer_rhs=read_rhs(pointer_symbol.symbol_expr(), loc);
  assert(pointer_rhs.id()==ID_symbol);

  unsigned init_value_level=expr.compound().get_unsigned_int(
    ID_it_init_value_level);
  const exprt init_pointer=get_pointer(expr.compound(), init_value_level-1);

  list_iteratort iterator(
    to_symbol_expr(pointer_rhs),
    init_pointer,
    get_iterator_fields(expr.compound()));

  auto it=iterators.insert(iterator);
  it.first->add_access(expr, inst_loc_number);
}

/// Create new iterator access
bool local_SSAt::all_symbolic_deref_defined(
  const exprt &expr,
  const namespacet &ns,
  locationt loc) const
{
  bool result=true;
  ssa_objectt ssa_object(expr, ns);
  if(ssa_object && has_symbolic_deref(ssa_object.get_expr()))
  {
    const ssa_domaint &ssa_domain=ssa_analysis[loc];
    auto def_it=ssa_domain.def_map.find(ssa_object.get_identifier());
    if(def_it==ssa_domain.def_map.end() || def_it->second.def.is_input())
      result=false;
  }
  else forall_operands(it, expr)
      result=result && all_symbolic_deref_defined(*it, ns, loc);
  return result;
}


/// Concretise symbolic rhs and return resulting expr
exprt local_SSAt::concretise_symbolic_deref_rhs(
  const exprt &rhs,
  const namespacet &ns,
  const locationt loc)
{
  const exprt deref_rhs=dereference(rhs, loc);
  const exprt symbolic_deref_rhs=symbolic_dereference(rhs, ns);
  ssa_objectt rhs_object(symbolic_deref_rhs, ns);

  if(deref_rhs.get_bool("#heap_access") && rhs_object)
  {
    if(can_reuse_symderef(rhs_object, ns, loc))
    {
      return symbolic_deref_rhs;
    }
    else
    {
      assign_rec(symbolic_deref_rhs, deref_rhs, true_exprt(), loc);
      return name(ssa_objectt(symbolic_deref_rhs, ns), OUT, loc);
    }
  }
  else
  {
    exprt rhs_copy=rhs;
    Forall_operands(it, rhs_copy)
    {
      *it=concretise_symbolic_deref_rhs(*it, ns, loc);
    }
    return rhs_copy;
  }

  return
    all_symbolic_deref_defined(symbolic_deref_rhs, ns, loc)?
      symbolic_deref_rhs:deref_rhs;
}

/// Collect allocation guards for the given location
void local_SSAt::collect_allocation_guards(
  const code_assignt &assign,
  locationt loc)
{
  if(!assign.rhs().get_bool("#malloc_result"))
    return;

  exprt rhs=assign.rhs();
  if(rhs.id()==ID_typecast)
    rhs=to_typecast_expr(rhs).op();
  if(rhs.id()==ID_if)
  {
    get_alloc_guard_rec(
      to_if_expr(rhs).true_case(), read_rhs(to_if_expr(rhs).cond(), loc));
    get_alloc_guard_rec(
      to_if_expr(rhs).false_case(),
      read_rhs(not_exprt(to_if_expr(rhs).cond()), loc));
  }
}

void local_SSAt::collect_record_frees(local_SSAt::locationt loc)
{
  if(loc->is_decl())
  {
    const exprt &symbol=to_code_decl(loc->code).symbol();
    if(symbol.id()!=ID_symbol)
      return;

    std::string id=id2string(to_symbol_expr(symbol).get_identifier());
    if(id.find("free::")!=std::string::npos &&
       id.find("::record")!=std::string::npos)
    {
      (--nodes.end())->record_free=symbol;
    }
  }
}

void local_SSAt::get_alloc_guard_rec(const exprt &expr, exprt guard)
{
  if(expr.id()==ID_symbol && expr.type().get_bool("#dynamic"))
  {
    allocation_guards.emplace(to_symbol_expr(expr).get_identifier(), guard);
  }
  else if(expr.id()==ID_if)
  {
    get_alloc_guard_rec(
      to_if_expr(expr).true_case(), and_exprt(guard, to_if_expr(expr).cond()));
    get_alloc_guard_rec(
      to_if_expr(expr).false_case(),
      and_exprt(guard, not_exprt(to_if_expr(expr).cond())));
  }
  else if(expr.id()==ID_typecast)
    get_alloc_guard_rec(to_typecast_expr(expr).op(), guard);
  else if(expr.id()==ID_address_of)
    get_alloc_guard_rec(to_address_of_expr(expr).object(), guard);
}

/// The symbolic dereference object can be reused if and only if the pointer it
/// dereferences was not overwritten and any potentially aliased object (or
/// field) was not overwritten.
/// \par parameters: Symbolic deference object, namespace, current location.
/// \return True if the symbolic dereference can be reused from the last
///   location that it was defined in (i.e. it does not have to be redefinef).
///   Otherwise false.
bool local_SSAt::can_reuse_symderef(
  ssa_objectt &symderef,
  const namespacet &ns,
  const local_SSAt::locationt loc)
{
  // Get a pointer that is dereferenced in the symbolic deref
  const exprt pointer=get_pointer(
    symderef.get_root_object(),
    pointed_level(symderef.get_root_object())-1);
  // Get the last definition of the pointer
  const auto pointer_id=ssa_objectt(pointer, ns).get_identifier();
  const auto pointer_def=ssa_analysis[loc].def_map.find(
    pointer_id)->second.def;
  // Get the last definition of the symbolic dereference
  const auto symbolic_id=symderef.get_identifier();
  const auto symbolic_def=ssa_analysis[loc].def_map.find(
    symbolic_id)->second.def;

  // If symbolic deref was not created yet, it cannot be reused.
  if(!symbolic_def.is_assignment())
    return false;

  // If the pointer that is dereferenced was overwritten, the symbolic deref
  // is not valid.
  if(pointer_def.is_assignment() && pointer_def.loc->location_number>
                                    symbolic_def.loc->location_number)
    return false;

  // Search all aliasing objects (objects potentially pointed by the pointer)
  const auto &values=ssa_value_ai[loc](pointer, ns);
  for(auto &obj : values.value_set)
  {
    irep_idt deref_id;
    if(symderef.get_expr().id()==ID_member)
    {
      auto member=member_exprt(
        obj.symbol_expr(),
        to_member_expr(symderef.get_expr()).get_component_name(),
        symderef.type());
      deref_id=ssa_objectt(member, ns).get_identifier();
    }
    else
    {
      deref_id=obj.get_identifier();
    }
    // If some potentially aliased object (or field) was overwritten,
    // the symbolic dereference cannot be reused.
    auto deref_def=ssa_analysis[loc].def_map.find(deref_id);
    if(deref_def!=ssa_analysis[loc].def_map.end() &&
       (deref_def->second.def.is_assignment() ||
        deref_def->second.def.is_phi()) &&
       deref_def->second.def.loc->location_number>
       symbolic_def.loc->location_number)
    {
      return false;
    }
  }

  return true;
}
