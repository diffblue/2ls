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
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
    unwind(*it,k);
}

/*****************************************************************************
 *
 *  Function : ssa_local_unwinder2t::unwind
 *
 *  Input : 
 *
 *  Output : 
 *
 *  Purpose : unwind all instances of given loop up to k starting from previous unwindings
 *
 *
 *****************************************************************************/

void ssa_local_unwinder2t::unwind(loopt &loop, unsigned k)
{
  for(loop_mapt::iterator it = loops.begin(); it != loops.end(); ++it)
  //TODO: identify instances -> odometer
  for(unsigned i = loop.current_unwinding; i<k; ++i)
  {
    add_loop_body(loop,unwindings);
    add_loop_connector(loop,unwindings);
  }
  SSA.increment_unwindings(-1);
  add_exit_merges(loop,unwindings,k);
  add_assertions(loop,unwindings,k);
  add_hoisted_assertions(loop,unwindings,k);
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

void ssa_local_unwinder2t::add_loop_body(loopt &loop, const odometert &unwindings)
{
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

void ssa_local_unwinder2t::add_loop_connector(loopt &loop,  const odometert &unwindings)
{
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

void ssa_local_unwinder2t::add_exit_merges(loopt &loop,  const odometert &unwindings, unsigned k)
{
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

void ssa_local_unwinder2t::add_assertions(loopt &loop,  const odometert &unwindings, unsigned k)
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

void ssa_local_unwinder2t::add_hoisted_assertions(loopt &loop,  const odometert &unwindings, unsigned k)
{
}
