/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

/// \file
/// SSA Unwinder

// #define DEBUG
#define COMPETITION

#include <util/prefix.h>

#include "ssa_unwinder.h"

/// builds data structures for unwinder and transforms SSA (rename to %0)
void ssa_local_unwindert::init()
{
  build_loop_tree();
  build_pre_post_map();
  build_exit_conditions();
  unwind(0);
#ifdef DEBUG
  SSA.output_verbose(std::cout);
#endif
}

void ssa_local_unwindert::build_loop_tree()
{
  // build loop tree structure
  // Assumes that initially the nodes are in the same order
  // as in the goto program
  std::list<local_SSAt::nodest::iterator> loopheads;
  local_SSAt::nodest::iterator n_it=--SSA.nodes.end();
  while(n_it!=SSA.nodes.begin())
  {
    // end of loop found
    if(n_it->loophead!=SSA.nodes.end())
    {
      loopt &loop=loops[n_it->loophead->location->location_number];
      if(loopheads.empty())
      {
        loop.is_root=true;
      }
      else
      {
        loops[loopheads.back()->location->location_number].
          loop_nodes.push_back(
            n_it->loophead->location->location_number);
      }
      loopheads.push_back(n_it->loophead);
      loop.body_nodes.push_front(*n_it);
#ifdef DEBUG
      std::cout << "pop " << n_it->location->location_number
                << " for " << n_it->loophead->location->location_number
                << std::endl;
#endif
      // this test is ambiguous if the loop condition is true,
      //  but shouldn't have any consequences
      assert(n_it->location->is_backwards_goto());
      loop.is_dowhile=!n_it->location->guard.is_true();
      SSA.nodes.erase(n_it--);
    }
    // beginning of loop found
    else if(!loopheads.empty() && n_it==loopheads.back())
    {
#ifdef DEBUG
      std::cout << "push " << n_it->location->location_number << std::endl;
#endif
      loops[n_it->location->location_number].body_nodes.push_front(*n_it);
      loopheads.pop_back();
      loops[n_it->location->location_number].body_nodes.back().loophead=
        loops[n_it->location->location_number].body_nodes.begin();
      SSA.nodes.erase(n_it--);
    }
    // collect loop body nodes
    else if(!loopheads.empty())
    {
#ifdef DEBUG
      std::cout << "add " << n_it->location->location_number
                << " for " << loopheads.back()->location->location_number
                << std::endl;
#endif
      loops[loopheads.back()->location->location_number].
        body_nodes.push_front(*n_it);
      SSA.nodes.erase(n_it--);
    }
    else
      --n_it;
  }
}

/// find variables at loop head and backedge
void ssa_local_unwindert::build_pre_post_map()
{
  for(loop_mapt::iterator it=loops.begin(); it!=loops.end(); ++it)
  {
    assert(!it->second.body_nodes.empty());
    const locationt &pre_loc=it->second.body_nodes.begin()->location;
    const locationt &post_loc=(--it->second.body_nodes.end())->location;
    SSA.current_location=pre_loc; // TODO: must go away

    // modified variables
    const ssa_domaint::phi_nodest &phi_nodes=
      SSA.ssa_analysis[pre_loc].phi_nodes;
    for(local_SSAt::objectst::const_iterator o_it=
           SSA.ssa_objects.objects.begin();
         o_it!=SSA.ssa_objects.objects.end(); o_it++)
    {
      ssa_domaint::phi_nodest::const_iterator p_it=phi_nodes.find(
        o_it->get_identifier());

      if(p_it==phi_nodes.end())
        continue; // object not modified in this loop

      it->second.modified_vars.push_back(o_it->get_expr());
      symbol_exprt pre=SSA.name(*o_it, local_SSAt::PHI, pre_loc);
      it->second.pre_post_map[pre]=SSA.read_rhs(*o_it, post_loc);
    }
  }
}

void ssa_local_unwindert::build_exit_conditions()
{
  for(loop_mapt::iterator it=loops.begin(); it!=loops.end(); ++it)
  {
    unsigned location_number_end=
      it->second.body_nodes.back().location->location_number;
#ifdef DEBUG
    std::cout << "end: " << location_number_end << std::endl;
#endif
    for(local_SSAt::nodest::iterator n_it=it->second.body_nodes.begin();
        n_it!=it->second.body_nodes.end(); n_it++)
    {
      if(!n_it->location->is_goto())
        continue;
      local_SSAt::nodest::iterator next=n_it; ++next;
      SSA.current_location=n_it->location; // TODO: must go away
      if(n_it->location->get_target()->location_number>location_number_end)
      {
        exprt g=SSA.guard_symbol(n_it->location);
        exprt c=SSA.cond_symbol(n_it->location);
        // need disjunction of all exit conditions
        //   for each symbol name at exit location
        for(exprt::operandst::const_iterator
               s_it=it->second.modified_vars.begin();
             s_it!=it->second.modified_vars.end(); s_it++)
        {
          exprt e=SSA.read_rhs(*s_it, n_it->location);
          it->second.exit_map[e].push_back(and_exprt(g, c));
        }
        it->second.exit_map[g].push_back(and_exprt(g, c));
        it->second.exit_map[c].push_back(and_exprt(g, c));
        // collect exits for assertion hoisting
        if(it->second.is_root)
        {
          it->second.assertion_hoisting_map[n_it->location->get_target()]
            .exit_conditions.push_back(and_exprt(g, c));
        }
      }
      else if(next==it->second.body_nodes.end() &&
              !n_it->location->guard.is_true())
      { // this happens in do-whiles
        // ENHANCE: transform goto-program to make SSA uniform in this respect
        exprt g=SSA.guard_symbol(n_it->location);
        exprt c=SSA.cond_symbol(n_it->location);
        for(exprt::operandst::const_iterator
               s_it=it->second.modified_vars.begin();
             s_it!=it->second.modified_vars.end(); s_it++)
        {
          exprt e=SSA.read_rhs(*s_it, n_it->location);
          it->second.exit_map[e].push_back(
            and_exprt(g, not_exprt(c)));
        }
        it->second.exit_map[g].push_back(and_exprt(g, not_exprt(c)));
        it->second.exit_map[c].push_back(and_exprt(g, not_exprt(c)));
        // collect exits for assertion hoisting
        if(it->second.is_root)
        {
          it->second.assertion_hoisting_map[n_it->location->get_target()]
            .exit_conditions.push_back(and_exprt(g, not_exprt(c)));
        }
      }
    }
  }
  // collect assertions for hoisting
  for(loop_mapt::iterator it=loops.begin(); it!=loops.end(); ++it)
  {
    if(!it->second.is_root)
      continue;
    for(loopt::assertion_hoisting_mapt::iterator
          h_it=it->second.assertion_hoisting_map.begin();
        h_it!=it->second.assertion_hoisting_map.end(); ++h_it)
    {
      local_SSAt::nodest::const_iterator n_it=SSA.nodes.begin();
      // find jump target in nodes
      while(n_it->location!=h_it->first &&
            n_it!=SSA.nodes.end()) ++n_it;
      local_SSAt::nodest::const_iterator prev=n_it;
      for(; n_it!=SSA.nodes.end(); ++n_it, ++prev)
      {
        // we collect only on top level, but not beyond loops
        //  so, if there is a gap in the nodes, we would jump over a loop
        if(n_it!=prev && // this would fail in the first iteration otherwise
           prev->location->location_number+1!=
           n_it->location->location_number)
          break;
        if(n_it==prev)
          --prev;
        for(local_SSAt::nodet::assertionst::const_iterator a_it=
               n_it->assertions.begin(); a_it!=n_it->assertions.end(); a_it++)
        {
          h_it->second.assertions.push_back(*a_it);
        }
      }
    }
  }
}

/// unwind all loops up to k starting from previous unwindings
void ssa_local_unwindert::unwind(unsigned k)
{
  if(SSA.current_unwinding>=(long)k)
    return;

  current_enabling_expr=
    symbol_exprt(
      "unwind::"+id2string(fname)+"::enable"+std::to_string(k),
      bool_typet());
  SSA.enabling_exprs.push_back(current_enabling_expr);

  // TODO: just for exploratory integration, must go away
  SSA.current_unwinding=k;

  // recursively unwind everything
  SSA.current_unwindings.clear();
  for(loop_mapt::iterator it=loops.begin(); it!=loops.end(); ++it)
  {
    if(!it->second.is_root)
      continue;
    unwind(it->second, k, false); // recursive
    assert(SSA.current_unwindings.empty());
  }
  // update current unwinding
  for(loop_mapt::iterator it=loops.begin(); it!=loops.end(); ++it)
  {
    it->second.current_unwinding=k;
  }
}

/// unwind all instances of given loop up to k starting from previous
/// unwindings, and recur
void ssa_local_unwindert::unwind(loopt &loop, unsigned k, bool is_new_parent)
{
  odometert context=SSA.current_unwindings;
#ifdef DEBUG
  std::cout << "unwind(k=" << k << ", is_new_parent=" << is_new_parent << "), ";
  std::cout << "context=" << SSA.odometer_to_string(context, context.size())
            << std::endl;
#endif
  SSA.increment_unwindings(1);
  for(long i=0; i<=k; ++i)
  {
    // add new unwindings of this loop
    if(i>loop.current_unwinding || is_new_parent)
    {
      add_loop_body(loop);
      // set new loop end node
      if(i==0)
      {
        assert(loop.end_nodes.find(context)==loop.end_nodes.end());
        loop.end_nodes[context]=--SSA.nodes.end();
        assert(loop.end_nodes.find(context)!=loop.end_nodes.end());
#ifdef DEBUG
        std::cout << "end node for context "
                  << SSA.odometer_to_string(context, context.size()) << ": "
                  << loop.end_nodes[context]->location->location_number << "=="
                  << loop.body_nodes.back().location->location_number
                  << std::endl;
#endif
      }
      if(i>0)
      {
        add_loop_connector(loop);
      }
      // in while loops we can only hoist in iterations %2 and higher
      //  otherwise we would block the loop exit that is only
      //  reachable via !guardls
      bool is_last=(loop.is_dowhile && i==0) ||
        (!loop.is_dowhile && (i==0 || i==1));
      add_assertions(loop, is_last);
      add_hoisted_assertions(loop, is_last);
    }
    if(i==k)
    {
      add_loop_head(loop);
      // update loop head
#ifdef DEBUG
      std::cout << "update loop head for context "
                << SSA.odometer_to_string(context, context.size()) << ": "
                << loop.body_nodes.begin()->location->location_number
                << std::endl;
#endif
      assert(loop.end_nodes.find(context)!=loop.end_nodes.end());
      loop.end_nodes[context]->loophead=--SSA.nodes.end();
      assert(
        loop.end_nodes[context]->loophead->location->location_number==
        loop.body_nodes.begin()->location->location_number);
    }
    // recurse into child loops
    for(const auto &l : loop.loop_nodes)
    {
#ifdef DEBUG
      std::cout << i << ">" << loop.current_unwinding << std::endl;
#endif
      unwind(loops[l], k, i>loop.current_unwinding || is_new_parent);
    }
    SSA.increment_unwindings(0);
  }
  SSA.increment_unwindings(-1);
  add_exit_merges(loop, k);
}

/// duplicates the loop body for the current instance
void ssa_local_unwindert::add_loop_body(loopt &loop)
{
  local_SSAt::nodest::iterator it=loop.body_nodes.begin();
  ++it; // skip loop head, we'll do that separately
  for(; it!=loop.body_nodes.end(); ++it)
  {
    if(it->equalities.empty() &&
       it->constraints.empty() &&
       it->function_calls.empty())
      continue;

#ifdef DEBUG
    std::cout << "add body node: "
              << it->location->location_number << std::endl;
#endif
    SSA.nodes.push_back(*it); // copy
    local_SSAt::nodet &node=SSA.nodes.back();
    node.loophead=SSA.nodes.end();
    node.marked=false;
    for(local_SSAt::nodet::equalitiest::iterator e_it=
           node.equalities.begin(); e_it!=node.equalities.end(); e_it++)
    {
      SSA.rename(*e_it, node.location);
    }
    for(local_SSAt::nodet::constraintst::iterator c_it=
           node.constraints.begin(); c_it!=node.constraints.end(); c_it++)
    {
      SSA.rename(*c_it, node.location);
    }
    for(local_SSAt::nodet::function_callst::iterator f_it=
           node.function_calls.begin();
         f_it!=node.function_calls.end(); f_it++)
    {
      SSA.rename(*f_it, node.location);
    }
    // will do assertions separately
    node.assertions.clear();
  }
}

/// adds the assertions and assumptions
void ssa_local_unwindert::add_assertions(loopt &loop, bool is_last)
{
  for(local_SSAt::nodest::iterator it=loop.body_nodes.begin();
      it!=loop.body_nodes.end(); ++it)
  {
    if(it->assertions.empty())
      continue;

    SSA.nodes.push_back(
      local_SSAt::nodet(it->location, SSA.nodes.end())); // add new node
    local_SSAt::nodet &node=SSA.nodes.back();
    node.assertions=it->assertions;
    SSA.current_location=node.location; // TODO: must go away
    for(local_SSAt::nodet::assertionst::iterator a_it=
           node.assertions.begin(); a_it!=node.assertions.end(); a_it++)
    {
      SSA.rename(*a_it, node.location);
      if(!is_last) // only add assumptions if we are not in %0 iteration
      {
        if(is_kinduction)
        {
          node.constraints.push_back(*a_it);
        }
        else if(is_bmc)
        {
          // only add in base case
          exprt gs=
            SSA.name(
              SSA.guard_symbol(),
              local_SSAt::LOOP_SELECT,
              loop.body_nodes.back().location);
          node.constraints.push_back(implies_exprt(not_exprt(gs), *a_it));
        }
      }
    }
    if(!is_last && (is_bmc || is_kinduction))
    {
      node.assertions.clear();
    }
  }
}

/// adds the new loop head
void ssa_local_unwindert::add_loop_head(loopt &loop)
{
  // new connecting loop head for the current instance
  //            (enabled for this iteration)
  SSA.nodes.push_back(loop.body_nodes.front()); // copy loop head
  local_SSAt::nodet &node=SSA.nodes.back();
  node.marked=false;
  node.enabling_expr=current_enabling_expr;
  for(local_SSAt::nodet::equalitiest::iterator e_it=
         node.equalities.begin(); e_it!=node.equalities.end(); e_it++)
  {
    SSA.rename(*e_it, node.location);
  }
  assert(node.constraints.empty());
  assert(node.function_calls.empty());
  assert(node.assertions.empty());
#ifdef DEBUG
  std::cout << "add loop head: " << node.location->location_number << std::endl;
#endif
}

/// adds a connector to the previous iteration
void ssa_local_unwindert::add_loop_connector(loopt &loop)
{
  // connector to previous iteration (permanently added)
  const local_SSAt::nodet &orig_node=loop.body_nodes.front();
  SSA.nodes.push_back(
    local_SSAt::nodet(orig_node.location, SSA.nodes.end())); // add new node
  local_SSAt::nodet &node=SSA.nodes.back();
  SSA.current_location=node.location; // TODO: must go away
  for(local_SSAt::nodet::equalitiest::const_iterator e_it=
         orig_node.equalities.begin();
       e_it!=orig_node.equalities.end(); e_it++)
  {
    if(e_it->rhs().id()==ID_if)
    {
      node.equalities.push_back(*e_it);
      node.equalities.back().rhs()=
        loop.pre_post_map[to_symbol_expr(e_it->lhs())];
      SSA.rename(node.equalities.back().rhs(), node.location);
      SSA.decrement_unwindings(0);
      SSA.rename(node.equalities.back().lhs(), node.location);
      SSA.increment_unwindings(0);
    }
    else if(e_it->lhs().id()==ID_symbol &&
            !has_prefix(
              id2string(to_symbol_expr(e_it->lhs()).get_identifier()),
              "ssa::$guard"))
    { // this is needed for while loops
      node.equalities.push_back(*e_it);
      SSA.decrement_unwindings(0);
      SSA.rename(node.equalities.back(), node.location);
      SSA.increment_unwindings(0);
    }
  }
  // continuation guard and condition
  exprt g_rhs=and_exprt(
    SSA.guard_symbol(loop.body_nodes.back().location),
    SSA.cond_symbol(loop.body_nodes.back().location));
  SSA.decrement_unwindings(0);
  exprt g_lhs=SSA.guard_symbol(loop.body_nodes.begin()->location);
  SSA.increment_unwindings(0);
  node.equalities.push_back(equal_exprt(g_lhs, g_rhs));
}

/// adds the merge connector for the loop exits for the current instance
void ssa_local_unwindert::add_exit_merges(loopt &loop, unsigned k)
{
  SSA.nodes.push_back(
    local_SSAt::nodet(
      loop.body_nodes.begin()->location,
      SSA.nodes.end())); // add new node
  local_SSAt::nodet &node=SSA.nodes.back();
  node.enabling_expr=current_enabling_expr;

  for(loopt::exit_mapt::const_iterator x_it=loop.exit_map.begin();
       x_it!=loop.exit_map.end(); x_it++)
  {
    node.equalities.push_back(
      build_exit_merge(
        x_it->first, disjunction(x_it->second), k, node.location));
  }
}

/// generates exit merge expression for a given expression
equal_exprt ssa_local_unwindert::build_exit_merge(
  exprt e, const exprt &exits, unsigned k, locationt loc)
{
  exprt re=e;
  SSA.increment_unwindings(1);
  SSA.rename(re, loc); // %0
  for(long i=1; i<=k; i++)
  {
    SSA.increment_unwindings(0);
    exprt cond_expr=exits;
    SSA.rename(cond_expr, loc);
    exprt true_expr=e;
    SSA.rename(true_expr, loc);
    exprt false_expr=re;
    re=if_exprt(cond_expr, true_expr, false_expr);
  }
  SSA.increment_unwindings(-1);
  SSA.rename(e, loc); // lhs
  return equal_exprt(e, re);
}

/// adds the assumptions for hoisted assertions for the current instance
void ssa_local_unwindert::add_hoisted_assertions(loopt &loop, bool is_last)
{
  for(loopt::assertion_hoisting_mapt::const_iterator
        it=loop.assertion_hoisting_map.begin();
      it!=loop.assertion_hoisting_map.end(); ++it)
  {
    if(!is_last // only add assumptions if we are not in %0 iteration
       && is_kinduction && !it->second.assertions.empty()
#ifdef COMPETITION
       && !(it->first->guard.id()==ID_not &&
            it->first->guard.op0().id()==ID_overflow_shl))
#endif
    {
      exprt e=disjunction(it->second.exit_conditions);
      SSA.rename(e, loop.body_nodes.begin()->location);
      SSA.nodes.push_back(
        local_SSAt::nodet(it->first, SSA.nodes.end())); // add new node
      local_SSAt::nodet &node=SSA.nodes.back();
      node.constraints.push_back(
        implies_exprt(e, conjunction(it->second.assertions)));
#ifdef DEBUG
      std::cout << "adding hoisted assumption: "
                << from_expr(SSA.ns, "", node.constraints.back())
                << std::endl;
#endif
    }
  }
}

/// return loop continuation conditions for all loops in this function
void ssa_local_unwindert::loop_continuation_conditions(
  exprt::operandst& loop_cont) const
{
  SSA.current_unwindings.clear();
  for(loop_mapt::const_iterator it=loops.begin(); it!=loops.end(); ++it)
  {
    if(!it->second.is_root)
      continue;
    loop_continuation_conditions(it->second, loop_cont); // recursive
    assert(SSA.current_unwindings.empty());
  }
}

exprt ssa_local_unwindert::get_continuation_condition(const loopt& loop) const
{
  SSA.current_location=loop.body_nodes.back().location; // TODO: must go away
  return and_exprt(
    SSA.guard_symbol(loop.body_nodes.back().location),
    SSA.cond_symbol(loop.body_nodes.back().location));
}

/// recursively construct loop continuation conditions
void ssa_local_unwindert::loop_continuation_conditions(
  const loopt& loop, exprt::operandst& loop_cont) const
{
  SSA.increment_unwindings(1);
  loop_cont.push_back(get_continuation_condition(loop)); // %0
  for(long i=0; i<=loop.current_unwinding; ++i)
  {
    // recurse into child loops
    for(const auto &l : loop.loop_nodes)
    {
      loop_continuation_conditions(loops.at(l), loop_cont);
    }
    SSA.increment_unwindings(0);
  }
  SSA.increment_unwindings(-1);
}

/// E.g. node must look like cond"somesuffix"==TRUE, e.g. cond%1%2%5%0==TRUE and
/// variable might be guard#ls25 if the current_unwinding is 6 the variable
/// should be converted to guard#ls25%1%2%5%5
///
///          Note that if current_unwinding is X then suffixes can have at most
///          X-1 in its parts
/// \par parameters: var, node
/// \return var is returned with a suffix that reflects the current unwinding
///   with the context taken from the node
void ssa_local_unwindert::unwinder_rename(
  symbol_exprt &var,
  const local_SSAt::nodet &node,
  bool pre) const
{
  // TODO: replace this by SSA.rename
  //      this requires odometer information in the nodes

  // only to be called for backedge nodes
  // This is very dirty hack
  if(SSA.current_unwinding<0)
    return;

  assert(node.equalities.size()>=1);
  // copy suffix from equality lhs to var
  std::string id=
    id2string(to_symbol_expr(node.equalities[0].op0()).get_identifier());
  size_t pos=id.find_first_of("%");
  if(pos==std::string::npos)
    return;
  size_t pos1=id.find_last_of("%");
  std::string suffix;
  unsigned unwinding=pre ? SSA.current_unwinding : 0;
  if(pos==pos1)
  {
    suffix="%"+std::to_string(unwinding);
  }
  else
  {
    suffix=id.substr(pos, pos1-pos);
    suffix+="%"+std::to_string(unwinding);
  }

  var.set_identifier(id2string(var.get_identifier())+suffix);
#ifdef DEBUG
  std::cout << "new id: " << var.get_identifier() << std::endl;
#endif
}


bool ssa_local_unwindert::find_loop(
  unsigned location_number, const loopt *&loop) const
{
  loop_mapt::const_iterator it=loops.find(location_number);
  if(it!=loops.end())
  {
    loop=&it->second;
    return true;
  }
  return false;
}

/// incrementally unwind a function 'id' up to depth k. Initializer must have
/// been invoked before calling this function
/// \param fname:name of the goto-function to be unwound, k-unwinding depth
/// \return false-if id does not correspond to any goto-function in the
///   unwinder_map
void ssa_unwindert::unwind(const irep_idt fname, unsigned int k)
{
  assert(is_initialized);
  unwinder_mapt::iterator it=unwinder_map.find(fname);
  assert(it!=unwinder_map.end());
  it->second.unwind(k);
}

void ssa_unwindert::unwind_all(unsigned int k)
{
  assert(is_initialized);

  for(auto &local_unwinder : unwinder_map)
    local_unwinder.second.unwind(k);
}

/// Initialize unwinder_map by computing hierarchical tree_loopnodet for every
/// goto-function Set is_initialized to true. Initializer must be called before
/// unwind funcitions are called.
void ssa_unwindert::init(bool is_kinduction, bool is_bmc)
{
  ssa_dbt::functionst& funcs=ssa_db.functions();
  for(auto &f : funcs)
  {
    unwinder_map.insert(
      unwinder_pairt(
        f.first,
        ssa_local_unwindert(f.first, (*(f.second)), is_kinduction, is_bmc)));
  }
}

void ssa_unwindert::init_localunwinders()
{
  for(auto &local_unwinder : unwinder_map)
    local_unwinder.second.init();
  is_initialized=true;
}
