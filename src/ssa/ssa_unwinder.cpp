/*******************************************************************\

Module: SSA Unwinder

Author: Peter Schrammel, Saurabh Joshi

\*******************************************************************/

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
  build_continuation_conditions();
  build_exit_conditions();
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
  std::list<local_SSAt::nodest::const_iterator> loopheads;
  local_SSAt::nodest::const_iterator n_it = SSA.nodes.end();
  do
  {
    --n_it;
    //end of loop found
    if (n_it->loophead != SSA.nodes.end())
    {
      loopt &loop = loops[n_it->loophead->location];
      if(loopheads.empty())
      {
	loop.is_root = true;
	loops[loopheads.back()->location].loop_nodes.push_back(n_it->loophead->location);
      }
      loopheads.push_back(n_it->loophead);
      loop.body_nodes.push_front(*n_it);
      //this test is ambiguous if the loop condition is true,
      //  but shouldn't have any consequences
      assert(n_it->location->is_backwards_goto());
      loop.is_dowhile = !n_it->location->guard.is_true();
    }
    //beginning of loop found
    if (n_it == loopheads.back())
    {
      loops[n_it->location].body_nodes.push_front(*n_it);
      loopheads.pop_back();
    }
    //collect loop body nodes
    if(!loopheads.empty())
    {
      loops[loopheads.back()->location].body_nodes.push_front(*n_it);
    }
  }
  while(n_it != SSA.nodes.begin());
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
    it->second.pre_post_map[SSA.guard_symbol(pre_loc)] = SSA.guard_symbol(post_loc);
    it->second.pre_post_map[SSA.cond_symbol(pre_loc)] = SSA.cond_symbol(post_loc);
    
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

      symbol_exprt pre = SSA.name(*o_it, local_SSAt::PHI,pre_loc);
      it->second.pre_post_map[pre] = SSA.read_rhs(*o_it, post_loc);
    }
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::build_continuation_conditions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : 
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::build_continuation_conditions()
{
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    if(it->second.is_dowhile) //take from post
    {
      //TODO
    }
    else  //take from pre
    {
      //TODO
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
      (--it->second.body_nodes.end())->location->location_number;
    for(local_SSAt::nodest::iterator n_it=it->second.body_nodes.begin();
	n_it!=it->second.body_nodes.end(); n_it++)
    {
      if(n_it->location->is_goto() &&
	 n_it->location->location_number>location_number_end)
      {
	it->second.exit_conditions.push_back(
	  and_exprt(SSA.guard_symbol(n_it->location),
		   SSA.cond_symbol(n_it->location)));
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
  current_enabling_expr = symbol_exprt(id2string(fname)+"::enable"+i2string(k),
				       bool_typet());
  //recursively unwind everything
  SSA.current_unwindings.clear();
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    if(!it->second.is_root)
      continue;
    unwind(it->second,k); //recursive
    assert(SSA.current_unwindings.empty());
  }
  //update current unwinding
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    it->second.current_unwinding=k;
  }
  SSA.current_unwinding = k; //TODO: just for exploratory integration, must go away
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

void ssa_local_unwindert::unwind(loopt &loop, unsigned k)
{
  SSA.increment_unwindings(1);
  for(unsigned i = 1; i<=k; ++i)
  {
    //add new unwindings of this loop
    if(i>loop.current_unwinding)
    {
      add_loop_body(loop,i==k);
      add_loop_connector(loop);
    }
    if(i==k)
      add_loop_head(loop);
    //recurse into child loops
    for(std::vector<locationt>::iterator l_it = loop.loop_nodes.begin();
	l_it != loop.loop_nodes.end(); ++l_it)
    {
      unwind(loops[*l_it],k);
    }
    SSA.increment_unwindings(0);
  }
  SSA.increment_unwindings(-1);
  add_exit_merges(loop,k);
  add_hoisted_assertions(loop,k);
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

void ssa_local_unwindert::add_loop_body(loopt &loop, bool is_last)
{
  local_SSAt::nodest::iterator it = loop.body_nodes.begin();
  ++it; //skip loop head, we'll do that separately
  for(; it != loop.body_nodes.end(); ++it)
  {
    SSA.nodes.push_back(*it); //copy
    local_SSAt::nodet &node = SSA.nodes.back();
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
    for (local_SSAt::nodet::assertionst::iterator a_it =
	   node.assertions.begin(); a_it != node.assertions.end(); a_it++)
    {
      SSA.rename(*a_it);
    }
    //transform assertions into assumptions in for incremental BMC and k-induction
    if(!is_last && (is_bmc || is_kinduction))
    {
      //TODO: while vs dowhile?
      for (local_SSAt::nodet::assertionst::iterator a_it =
	     node.assertions.begin(); a_it != node.assertions.end(); a_it++)
      {
	node.constraints.push_back(*a_it);
      }
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
  SSA.nodes.push_back(loop.body_nodes.front()); //copy loop head
  local_SSAt::nodet &node=SSA.nodes.back();
  node.marked = false;
  for (local_SSAt::nodet::equalitiest::iterator e_it =
	 node.equalities.begin(); e_it != node.equalities.end(); e_it++)
  {
    if(e_it->rhs().id() == ID_if || //phi
       e_it->lhs() == SSA.guard_symbol(node.location)) 
    {
      e_it->rhs() = loop.pre_post_map[to_symbol_expr(e_it->lhs())]; 
      SSA.rename(e_it->rhs());
      SSA.decrement_unwindings(0);
      SSA.rename(e_it->lhs());
      SSA.increment_unwindings(0);
    }
    else
    {
      SSA.rename(*e_it);
    }
  }
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
  node.assertions.clear();
  node.constraints.clear();
  node.templates.clear();
  node.enabling_expr = current_enabling_expr;
  exprt exits = disjunction(loop.exit_conditions);

  for (local_SSAt::nodet::equalitiest::iterator e_it =
	 node.equalities.begin(); e_it != node.equalities.end(); e_it++)
  {
    exprt e = e_it->lhs();
    exprt re = e_it->lhs();
    SSA.increment_unwindings(1);
    SSA.rename(re); //%0
    for (unsigned int i = 1; i < k; i++)
    {
      exprt cond_expr = exits;
      SSA.rename(cond_expr);
      exprt true_expr = e;
      SSA.rename(true_expr);
      exprt false_expr = re;
      re = if_exprt(cond_expr, true_expr, false_expr);
      SSA.increment_unwindings(0);
    }
    SSA.increment_unwindings(-1);
    SSA.rename(e); //lhs
    node.equalities.push_back(equal_exprt(e,re));
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwindert::add_hoisted_assertions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the hoisted assumptions and assertions for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwindert::add_hoisted_assertions(loopt &loop, unsigned k)
{
      //TODO
}

/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::output
 *
 * Input :
 *
 * Output :
 *
 * Purpose : output loop info
 *
 *****************************************************************************/

void ssa_local_unwindert::output(std::ostream& out, const namespacet& ns)
{
  // TODO
}

/*****************************************************************************\
 *
 * Function : ssa_local_unwindert::output
 *
 * Input :
 *
 * Output :
 *
 * Purpose : output local unwinder info
 *
 *****************************************************************************/

void ssa_local_unwindert::output(std::ostream& out)
{
  // TODO
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
  for(loop_mapt::const_iterator it = loops.begin(); it != loops.end(); ++it)
  {
    loop_cont.push_back(it->second.continuation_condition);
  }
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
  
  //only to be called for backedge nodes
  //This is very dirty hack :-(
  if(SSA.current_unwinding==0) return;
  assert(node.equalities.size()>=1);
  //copy suffix from equality lhs to var
  std::string id = 
    id2string(to_symbol_expr(node.equalities[0].op0()).get_identifier());
  size_t pos = id.find_first_of("%");
  if(pos==std::string::npos) return;
  size_t pos1 = id.find_last_of("%");
  std::string suffix;
  unsigned unwinding = pre ? SSA.current_unwinding-1 : 0;
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
 * Function : ssa_unwindert::output
 *
 * Input :
 *
 * Output :
 *
 * Purpose :
 *
 *****************************************************************************/

void ssa_unwindert::output(std::ostream & out) {
  if(!is_initialized) return;
  for (unwinder_mapt::iterator it = unwinder_map.begin();
       it != unwinder_map.end(); it++) {
    out << "Unwinding for function" << it->first << std::endl;
    it->second.output(out);
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
