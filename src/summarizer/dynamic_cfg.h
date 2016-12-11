/*******************************************************************\

Module: Global Control Flow Graph

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_SUMMARIZER_GLOBAL_CFG_H
#define CPROVER_2LS_SUMMARIZER_GLOBAL_CFG_H

#include <util/std_expr.h>
#include <util/graph.h>

#include "goto_functions.h"

/*******************************************************************\

   Class: global_cfgt

 Purpose:

\*******************************************************************/

struct global_cfg_edget
{
};

struct global_cfg_idt
{
  goto_programt::const_target pc;
  std::vector<unsigned> iteration_stack;
  //TODO: thread id
}

struct global_cfg_nodet:public graph_nodet<global_cfg_edget>
{
  global_cfg_idt id;
  bool is_loop_head;
  exprt assumption;
};

class global_cfgt:public graph<global_cfg_nodet>
{
public:
  // TODO: generalise this to non-inlined programs
  void operator()(
    const ssa_local_unwindert &ssa_unwinder,
    const goto_programt &goto_program);

  
protected:
  typedef std::map<global_cfg_idt, exprt> assumptionst;

  void build_from_invariants(assumptionst &assumptions);
//  void build_from_assumptions(assumptionst &assumptions);
  void add_assumptions(assumptionst assumptions);

};

#endif // CPROVER_2LS_SUMMARIZER_GLOBAL_CFG_H
