/*******************************************************************\

Module: SSA Unwinder

Author: Saurabh Joshi, Peter Schrammel

\*******************************************************************/

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::init
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : builds data structures for unwinder and transforms SSA (rename to %0)
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::init()
{
  //build loop tree structure
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
    }
    //beginning of loop found
    if (n_it == loopheads.back())
    {
      loop.body_nodes.push_front(*n_it);
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
 *  Function : ssa_local_unwinder2t::unwind
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : unwind all loops up to k starting from previous unwindings
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::unwind(unsigned k)
{
  //recursively unwind everything
  SSA.current_unwindings.clear();
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    if(!it->is_root)
      continue;
    unwind(*it,k); //recursive
    assert(SSA.current_unwindings.empty());
  }
  //update current unwinding
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  {
    it->current_unwinding=k;
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::unwind
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

void ssa_local_unwinder2t::unwind(loopt &loop, unsigned k)
{
  SSA.increment_unwindings(1);
  for(unsigned i = 0; i<k; ++i)
  {
    //add new unwindings of this loop
    if(i>loop.current_unwinding)
    {
      add_loop_body(loop);
      add_loop_connector(loop);
    }
    //recurse into child loops
    for(loop_mapt::iterator l_it = it->loop_nodes.begin();
	l_it != it->loop_nodes.end(); ++l_it)
    {
      unwind(*l_it,k);
    }
    SSA.increment_unwindings(0);
  }
  SSA.increment_unwindings(-1);
  add_exit_merges(loop,SSA.current_unwindings,k);
  //TODO: not sure whether these could go into loop above
  add_assertions(loop,SSA.current_unwindings,k); 
  add_hoisted_assertions(loop,SSA.current_unwindings,k);
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::add_loop_body
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : duplicates the loop body for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::add_loop_body(loopt &loop)
{
  local_SSAt::nodest::iterator it = loop.body_nodes.begin();
  ++it; //skip loop head
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
    //we'll do assertions later
    node.assertions.clear();
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::add_loop_connector
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the loop connectors for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::add_loop_connector(loopt &loop)
{
  SSA.nodes.push_back(loop.body_nodes.front());
  local_SSAt::nodet &node=SSA.nodes.back();
  for (local_SSAt::nodet::equalitiest::iterator e_it =
	 node.equalities.begin(); e_it != node.equalities.end(); e_it++)
  {
    if (e_it->rhs().id() == ID_if) //TODO
    {
      if_exprt &e = to_if_expr(e_it->rhs());
      e_it->rhs() = current_loop.pre_post_exprs[e.true_case()]; //TODO
      rename(e_it->rhs(), suffix, i,current_loop);
      rename(e_it->lhs(), suffix, i-1,current_loop);
    }
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::add_exit_merges
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the merge connector for the loop exits for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::add_exit_merges(loopt &loop, odometert unwindings, unsigned k)
{
  SSA.nodes.push_back(loop.body_nodes.front());
  local_SSAt::nodet &node=SSA.nodes.back();
  node.marked = false;
  node.equalities.clear();
  node.assertions.clear();
  node.constraints.clear();
  node.templates.clear();

  for(expr_break_mapt::iterator e_it=current_loop.connectors.begin();  //TODO
      e_it!=current_loop.connectors.end();e_it++)
  {
    exprt e = e_it->first;
    exprt re = e;
    rename(re, suffix, 0,current_loop); //TODO
    for (unsigned int i = 1; i < unwind_depth; i++)
    {
      exprt cond_expr = e_it->second;
      rename(cond_expr,suffix,i,current_loop); //TODO
      exprt true_expr = e;
      rename(true_expr, suffix,i,current_loop); //TODO
      exprt false_expr = re;
      re = if_exprt(cond_expr, true_expr, false_expr);
    }
    exprt rhs = re;
    exprt lhs = e;

    rename(lhs,suffix,-1,current_loop); //TODO
    node.equalities.push_back(equal_exprt(lhs,rhs));

    node.enabling_expr = new_sym;
  }
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::add_assertions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds assumptions and assertions for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::add_assertions(loopt &loop,  odometert unwindings, unsigned k)
{
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::add_hoisted_assertions
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : adds the hoisted assumptions and assertions for the current instance
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::add_hoisted_assertions(loopt &loop,  odometert unwindings, unsigned k)
{
}
