/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

#include <util/prefix.h>

#include "ssa_unwinder.h"

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::init
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : builds data structures for unwinder and transforms SSA (rename to %0)
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::init()
{
  build_loop_tree();
  build_pre_post_map();
  build_exit_conditions();
  unwind(0);
#if 1
  SSA.output_verbose(std::cout);
#endif
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::build_loop_tree
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : 
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::build_loop_tree()
{
  //build loop tree structure
  //Assumes that initially the nodes are in the same order as in the goto program
  std::list<local_SSAt::nodest::iterator> loopheads;
  local_SSAt::nodest::iterator n_it = --SSA.nodes.end();
  while(n_it != SSA.nodes.begin())
  {
    //end of loop found
    if (n_it->loophead != SSA.nodes.end())
    {
      loopt &loop = loops[n_it->loophead->location];
      if(loopheads.empty())
      {
	loop.is_root = true;
      }
      else 
      {
	loops[loopheads.back()->location].loop_nodes.push_back(
	  n_it->loophead->location);
      }
      loopheads.push_back(n_it->loophead);
      loop.body_nodes.push_front(*n_it);
#if 1
    std::cout << "pop " << n_it->location->location_number 
      << " for " << n_it->loophead->location->location_number << std::endl;
#endif
      //this test is ambiguous if the loop condition is true,
      //  but shouldn't have any consequences
      assert(n_it->location->is_backwards_goto());
      loop.is_dowhile = !n_it->location->guard.is_true();
      SSA.nodes.erase(n_it--);
    }
    //beginning of loop found
    else if (n_it == loopheads.back())
    {
#if 1
    std::cout << "push " << n_it->location->location_number << std::endl;
#endif
      loops[n_it->location].body_nodes.push_front(*n_it);
      loopheads.pop_back();
      loops[n_it->location].body_nodes.back().loophead = 
	loops[n_it->location].body_nodes.begin();
      SSA.nodes.erase(n_it--);
    }
    //collect loop body nodes
    else if(!loopheads.empty())
    {
#if 1
    std::cout << "add " << n_it->location->location_number 
      << " for " << loopheads.back()->location->location_number << std::endl;
#endif
      loops[loopheads.back()->location].body_nodes.push_front(*n_it);
      SSA.nodes.erase(n_it--);
    }
    else 
      --n_it;
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::build_pre_post_map
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : find variables at loop head and backedge
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::build_pre_post_map()
{
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    assert(!it->second.body_nodes.empty());
    const locationt &pre_loc = it->second.body_nodes.begin()->location;
    const locationt &post_loc = (--it->second.body_nodes.end())->location;

    //guards and conditions
/*    it->second.pre_post_map[SSA.guard_symbol(pre_loc)] = 
      SSA.guard_symbol(post_loc);
    it->second.pre_post_map[SSA.cond_symbol(pre_loc)] = 
    SSA.cond_symbol(post_loc);*/

    //modified variables
    const ssa_domaint::phi_nodest &phi_nodes =
      SSA.ssa_analysis[pre_loc].phi_nodes;
    for (local_SSAt::objectst::const_iterator o_it =
	   SSA.ssa_objects.objects.begin();
	 o_it != SSA.ssa_objects.objects.end(); o_it++)
    {
      ssa_domaint::phi_nodest::const_iterator p_it = phi_nodes.find(
	o_it->get_identifier());

      if (p_it == phi_nodes.end())
	continue; // object not modified in this loop

      it->second.modified_vars.push_back(o_it->get_expr());
      symbol_exprt pre = SSA.name(*o_it, local_SSAt::PHI,pre_loc);
      it->second.pre_post_map[pre] = SSA.read_rhs(*o_it, post_loc);
    }
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::build_exit_conditions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : 
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::build_exit_conditions()
{
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    unsigned location_number_end =
      it->second.body_nodes.back().location->location_number;
#if 0
    std::cout << "end: " << location_number_end << std::endl;
#endif
    for(local_SSAt::nodest::iterator n_it=it->second.body_nodes.begin();
	n_it!=it->second.body_nodes.end(); n_it++)
    {
      if(!n_it->location->is_goto())
	continue;
      local_SSAt::nodest::iterator next = n_it; ++next;
      if(n_it->location->get_target()->location_number>location_number_end)
      {
	exprt g = SSA.guard_symbol(n_it->location);
	exprt c = SSA.cond_symbol(n_it->location);
        //need disjunction of all exit conditions 
        //   for each symbol name at exit location
	for (exprt::operandst::const_iterator 
	       s_it = it->second.modified_vars.begin(); 
	     s_it != it->second.modified_vars.end(); s_it++)
	{
	  exprt e = SSA.read_rhs(*s_it,n_it->location);
	  it->second.exit_map[e].push_back(and_exprt(g,c));
	}
	it->second.exit_map[g].push_back(and_exprt(g,c));
	it->second.exit_map[c].push_back(and_exprt(g,c));
	//TODO: collected assertions for hoisting
      }
      else if(next==it->second.body_nodes.end() && 
	      !n_it->location->guard.is_true())
      { //this happens in do-whiles 
        //ENHANCE: transform goto-program to make SSA uniform in this respect
	exprt g = SSA.guard_symbol(n_it->location);
	exprt c = SSA.cond_symbol(n_it->location);
	for (exprt::operandst::const_iterator 
	       s_it = it->second.modified_vars.begin(); 
	     s_it != it->second.modified_vars.end(); s_it++)
	{
	  exprt e = SSA.read_rhs(*s_it,n_it->location);
	  it->second.exit_map[e].push_back( 
	    and_exprt(g,not_exprt(c)));
	}
	it->second.exit_map[g].push_back(and_exprt(g,not_exprt(c)));
	it->second.exit_map[c].push_back(and_exprt(g,not_exprt(c)));
	//TODO: collected assertions for hoisting
      }
    }
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::unwind
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : unwind all loops up to k starting from previous unwindings
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::unwind(unsigned k)
{
  if(SSA.current_unwinding >= k)
    return;

  current_enabling_expr = 
    symbol_exprt("unwind::"+id2string(fname)+"::enable"+i2string(k),
		 bool_typet());
  SSA.enabling_exprs.push_back(current_enabling_expr);
  SSA.current_unwinding = k; //TODO: just for exploratory integration, must go away
  //recursively unwind everything
  SSA.current_unwindings.clear();
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    if(!it->second.is_root)
      continue;
    unwind(it->second,k,false); //recursive
    assert(SSA.current_unwindings.empty());
  }
  //update current unwinding
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    it->second.current_unwinding=k;
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::unwind
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : unwind all instances of given loop up to k 
              starting from previous unwindings,
              and recurse
 *
 *****************************************************************************/

void ssa_local_unwindert::unwind(loopt &loop, unsigned k, bool is_new_parent)
{
  odometert context = SSA.current_unwindings;
  SSA.increment_unwindings(1);
  for(unsigned i = 0; i<=k; ++i)
  {
    //add new unwindings of this loop
    if(i>loop.current_unwinding || is_new_parent)
    {
      add_loop_body(loop);
      //set new loop end node
      if(i==0)
      {
	assert(loop.end_nodes.find(context) == loop.end_nodes.end());
	loop.end_nodes[context] = --SSA.nodes.end();
        assert(loop.end_nodes.find(context) != loop.end_nodes.end());
#if 1
	std::cout << "end node for context "
		  << SSA.odometer_to_string(context,context.size()) << ": "
	    << loop.end_nodes[context]->location->location_number << " == " 
	    << loop.body_nodes.back().location->location_number << std::endl;
#endif
      }
      if(i>0)
      {
        add_loop_connector(loop);
      }
    }
    if(i==k)
    {
      add_loop_head(loop);
      //update loop head
#if 1
	std::cout << "update loop head for context "
		  << SSA.odometer_to_string(context,context.size()) << ": "
		  << loop.body_nodes.begin()->location->location_number << std::endl;
#endif
      assert(loop.end_nodes.find(context) != loop.end_nodes.end());
      loop.end_nodes[context]->loophead = --SSA.nodes.end();
      assert(loop.end_nodes[context]->loophead->location->location_number == 
	     loop.body_nodes.begin()->location->location_number);
    }
    add_assertions(loop,i==0);
    add_hoisted_assertions(loop,i==0);
    //recurse into child loops
    for(std::vector<locationt>::iterator l_it = loop.loop_nodes.begin();
	l_it != loop.loop_nodes.end(); ++l_it)
    {
      unwind(loops[*l_it],k,i>loop.current_unwinding);
    }
    SSA.increment_unwindings(0);
  }
  SSA.increment_unwindings(-1);
  add_exit_merges(loop,k);
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_loop_body
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : duplicates the loop body for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::add_loop_body(loopt &loop)
{
  local_SSAt::nodest::iterator it = loop.body_nodes.begin();
  ++it; //skip loop head, we'll do that separately
  for(; it != loop.body_nodes.end(); ++it)
  {
    if(it->equalities.empty() && 
       it->constraints.empty() &&
       it->function_calls.empty())
      continue;

#if 1
    std::cout << "add body node: " 
	      << it->location->location_number << std::endl;
#endif
    SSA.nodes.push_back(*it); //copy
    local_SSAt::nodet &node = SSA.nodes.back();
    node.loophead = SSA.nodes.end();
    node.marked = false;
    for (local_SSAt::nodet::equalitiest::iterator e_it =
	   node.equalities.begin(); e_it != node.equalities.end(); e_it++)
    {
      SSA.rename(*e_it);
    }
    for (local_SSAt::nodet::constraintst::iterator c_it =
	   node.constraints.begin(); c_it != node.constraints.end(); c_it++)
    {
      SSA.rename(*c_it);
    }
    for (local_SSAt::nodet::function_callst::iterator f_it =
	   node.function_calls.begin(); f_it != node.function_calls.end(); f_it++)
    {
      SSA.rename(*f_it);
    }
    //will do assertions separately
    node.assertions.clear();
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_assertions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the new loop head
 *
 *****************************************************************************/

void ssa_local_unwindert::add_assertions(loopt &loop, bool is_last)
{
  
  for(local_SSAt::nodest::iterator it = loop.body_nodes.begin(); 
      it != loop.body_nodes.end(); ++it)
  {
    if(it->assertions.empty())
      continue;

    SSA.nodes.push_back(*it); //copy
    local_SSAt::nodet &node = SSA.nodes.back();
    node.equalities.clear();
    node.constraints.clear();
    node.function_calls.clear();
    node.templates.clear();
    for (local_SSAt::nodet::assertionst::iterator a_it =
	   node.assertions.begin(); a_it != node.assertions.end(); a_it++)
    {
      SSA.rename(*a_it);
      if(!is_last) //only add assumptions if we are not in %0 iteration
      {
        if(is_kinduction) 
	  node.constraints.push_back(*a_it);
	else if(is_bmc)
	{
	  //only add in base case
	  exprt gs = SSA.name(SSA.guard_symbol(), 
	    local_SSAt::LOOP_SELECT, loop.body_nodes.back().location);
	  node.constraints.push_back(implies_exprt(not_exprt(gs),*a_it));
	}
      }
    }
    if(!is_last && (is_bmc || is_kinduction))
    {
      node.assertions.clear();
    }
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_loop_head
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the new loop head
 *
 *****************************************************************************/

void ssa_local_unwindert::add_loop_head(loopt &loop)
{
  // new connecting loop head for the current instance
  //            (enabled for this iteration)
  SSA.nodes.push_back(loop.body_nodes.front()); //copy loop head
  local_SSAt::nodet &node=SSA.nodes.back();
  node.marked = false;
  node.enabling_expr = current_enabling_expr;
  for (local_SSAt::nodet::equalitiest::iterator e_it =
	 node.equalities.begin(); e_it != node.equalities.end(); e_it++)
  {
    SSA.rename(*e_it);
  }
#if 1
  std::cout << "add loop head: " << node.location->location_number << std::endl;
#endif
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_loop_connector
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds a connector to the previous iteration
 *
 *****************************************************************************/

void ssa_local_unwindert::add_loop_connector(loopt &loop)
{
  // connector to previous iteration (permanently added)
  const local_SSAt::nodet &orig_node=loop.body_nodes.front();
  SSA.nodes.push_back(loop.body_nodes.front()); //copy loop head
  local_SSAt::nodet &node=SSA.nodes.back();
  node.equalities.clear();
  node.function_calls.clear();
  node.constraints.clear();
  node.templates.clear();
  node.assertions.clear();
  node.marked = false;
  for (local_SSAt::nodet::equalitiest::const_iterator e_it =
	 orig_node.equalities.begin(); 
       e_it != orig_node.equalities.end(); e_it++)
  {
    if(e_it->rhs().id()==ID_if)
    {
      node.equalities.push_back(*e_it);
      node.equalities.back().rhs() = 
	loop.pre_post_map[to_symbol_expr(e_it->lhs())]; 
      SSA.rename(node.equalities.back().rhs());
      SSA.decrement_unwindings(0);
      SSA.rename(node.equalities.back().lhs());
      SSA.increment_unwindings(0);
    }
    else if(e_it->lhs().id()==ID_symbol &&
	    !has_prefix(id2string(to_symbol_expr(e_it->lhs()).get_identifier()),
		       "ssa::$guard"))
    { //this is needed for while loops
      node.equalities.push_back(*e_it);
      SSA.decrement_unwindings(0);
      SSA.rename(node.equalities.back());
      SSA.increment_unwindings(0);
    }
  }
  //continuation guard and condition
  exprt g_rhs = and_exprt(SSA.guard_symbol(loop.body_nodes.back().location),
			  SSA.cond_symbol(loop.body_nodes.back().location));
  SSA.decrement_unwindings(0);
  exprt g_lhs = SSA.guard_symbol(loop.body_nodes.begin()->location);
  SSA.increment_unwindings(0);
  node.equalities.push_back(equal_exprt(g_lhs,g_rhs));
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_exit_merges
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the merge connector for the loop exits for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::add_exit_merges(loopt &loop, unsigned k)
{
  SSA.nodes.push_back(loop.body_nodes.front()); //copy loop head
  local_SSAt::nodet &node=SSA.nodes.back();
  node.marked = false;
  node.equalities.clear();
  node.constraints.clear();
  node.function_calls.clear();
  node.templates.clear();
  node.assertions.clear();
  node.enabling_expr = current_enabling_expr;

  for (loopt::exit_mapt::const_iterator x_it = loop.exit_map.begin();
       x_it != loop.exit_map.end(); x_it++)
  {
    node.equalities.push_back(build_exit_merge(x_it->first,
					       disjunction(x_it->second),k));
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::build_exit_merge
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : generates exit merge expression for a given expression
 *
 *****************************************************************************/

equal_exprt ssa_local_unwindert::build_exit_merge(
  exprt e, const exprt &exits, unsigned k)
{
  exprt re = e;
  SSA.increment_unwindings(1);
  SSA.rename(re); //%0
  for (unsigned i = 1; i <= k; i++)
  {
    SSA.increment_unwindings(0);
    exprt cond_expr = exits;
    SSA.rename(cond_expr);
    exprt true_expr = e;
    SSA.rename(true_expr);
    exprt false_expr = re;
    re = if_exprt(cond_expr, true_expr, false_expr);
  }
  SSA.increment_unwindings(-1);
  SSA.rename(e); //lhs
  return equal_exprt(e,re);
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_hoisted_assertions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the hoisted assumptions and assertions 
              for the current instance
 *
 *****************************************************************************/

void ssa_local_unwindert::add_hoisted_assertions(loopt &loop, bool is_last)
{
  for(assertion_hoisting_mapt::const_iterator 
	it = assertion_hoisting_map.begin(); 
      it != assertion_hoisting_map.end(); ++it)
  {
  }
}

/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::loop_continuation_conditions
 *
 * Input :
 *
 * Output :
 *
 * Purpose : return loop continuation conditions for all loops in this function
 *
 *****************************************************************************/

void ssa_local_unwindert::loop_continuation_conditions(
  exprt::operandst& loop_cont) const
{
  SSA.current_unwindings.clear();
  for(loop_mapt::const_iterator it = loops.begin(); it != loops.end(); ++it)
  {
    if(!it->second.is_root)
      continue;
    loop_continuation_conditions(it->second,loop_cont); //recursive
    assert(SSA.current_unwindings.empty());
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::get_continuation_condition
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : 
 *
 *
 *****************************************************************************/

exprt ssa_local_unwindert::get_continuation_condition(const loopt& loop) const
{
  return and_exprt(SSA.guard_symbol(loop.body_nodes.back().location),
   	        SSA.cond_symbol(loop.body_nodes.back().location));
}

/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::loop_continuation_conditions
 *
 * Input :
 *
 * Output :
 *
 * Purpose : recursively construct loop continuation conditions
 *
 *****************************************************************************/

void ssa_local_unwindert::loop_continuation_conditions(
  const loopt& loop, exprt::operandst& loop_cont) const
{
  SSA.increment_unwindings(1);
  loop_cont.push_back(get_continuation_condition(loop)); //%0
  for(unsigned i=0; i<=loop.current_unwinding; ++i)
  {
    //recurse into child loops
    for(std::vector<locationt>::const_iterator l_it = loop.loop_nodes.begin();
	l_it != loop.loop_nodes.end(); ++l_it)
    {
      loop_continuation_conditions(loops.at(*l_it),loop_cont);
    }
    SSA.increment_unwindings(0);
  }
  SSA.increment_unwindings(-1);
}


/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::unwinder_rename
 *
 * Input : var, node
 *
 * Output : var is returned with a suffix that reflects the current unwinding
 *          with the context taken from the node
 *
 *          E.g.
 *
 *          node must look like
 *
 *          cond"somesuffix" == TRUE
 *
 *          e.g. cond%1%2%5%0 == TRUE
 *
 *          and variable might be guard#ls25
 *
 *          if the current_unwinding is 6
 *
 *          the variable should be converted to guard#ls25%1%2%5%5
 *
 *          Note that if current_unwinding is X then suffixes can have at most
 *          X-1 in its parts
 *
 *****************************************************************************/

void ssa_local_unwindert::unwinder_rename(symbol_exprt &var,
  const local_SSAt::nodet &node, bool pre) const
{
  //TODO: replace this by SSA.rename
  //      this requires odometer information in the nodes
  
  //only to be called for backedge nodes
  //This is very dirty hack :-(
  if(SSA.current_unwinding<0) return;
  assert(node.equalities.size()>=1);
  //copy suffix from equality lhs to var
  std::string id = 
    id2string(to_symbol_expr(node.equalities[0].op0()).get_identifier());
  size_t pos = id.find_first_of("%");
  if(pos==std::string::npos) return;
  size_t pos1 = id.find_last_of("%");
  std::string suffix;
  unsigned unwinding = pre ? SSA.current_unwinding : 0;
  if(pos==pos1)
  {
     suffix = "%"+i2string(unwinding);
  }
  else
  {
    suffix = id.substr(pos,pos1-pos);
    suffix += "%"+i2string(unwinding);
  }

  var.set_identifier(id2string(var.get_identifier())+suffix);
#ifdef DEBUG
  std::cout << "new id: " << var.get_identifier() << std::endl;
#endif
}

/*****************************************************************************\
 *
 * Function : ssa_unwindert::unwind
 *
 * Input : fname - name of the goto-function to be unwound, k - unwinding depth
 *
 * Output : false - if id does not correspond to any goto-function in the
 * 			unwinder_map
 *
 * Purpose : incrementally unwind a function 'id' up to depth k. Initializer
 * must have been invoked before calling this function
 *
 *****************************************************************************/

void ssa_unwindert::unwind(const irep_idt fname, unsigned int k)
{
  assert(is_initialized);
  unwinder_mapt::iterator it = unwinder_map.find(fname);
  assert(it != unwinder_map.end());
  it->second.unwind(k);
}

/*****************************************************************************\
 *
 * Function : ssa_unwindert::unwind_all
 *
 * Input :
 *
 * Output :
 *
 * Purpose :
 *
 *****************************************************************************/

void ssa_unwindert::unwind_all(unsigned int k)
{
  assert(is_initialized);

  for (unwinder_mapt::iterator it = unwinder_map.begin();
       it != unwinder_map.end(); it++) {
    it->second.unwind(k);
  }
}

/*****************************************************************************\
 *
 * Function : ssa_unwindert::init
 *
 * Input :
 *
 * Output :
 *
 * Purpose : Initialize unwinder_map by computing hierarchical tree_loopnodet
 *           for every goto-function
 *           Set is_initialized to true. Initializer must be called before
 *           unwind funcitions are called.
 *
 *****************************************************************************/
void ssa_unwindert::init(bool is_kinduction, bool is_bmc)
{
  ssa_dbt::functionst& funcs = ssa_db.functions();
  for (ssa_dbt::functionst::iterator it = funcs.begin();
       it != funcs.end(); it++)
  {
    unwinder_map.insert(unwinder_pairt(it->first,
      ssa_local_unwindert(it->first, (*(it->second)),
  		          is_kinduction, is_bmc)));
  }
}

/*****************************************************************************\
 *
 * Function : ssa_unwindert::init_localunwinders
 *
 * Input :
 *
 * Output :
 *
 * Purpose :
 *
 *****************************************************************************/

void ssa_unwindert::init_localunwinders()
{
  for(unwinder_mapt::iterator it=unwinder_map.begin();
      it!=unwinder_map.end();it++)
  {
    it->second.init();
  }
  is_initialized = true;
}
