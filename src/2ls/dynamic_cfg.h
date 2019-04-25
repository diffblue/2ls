/*******************************************************************\

Module: Dynamic Control Flow Graph

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Dynamic Control Flow Graph

#ifndef CPROVER_2LS_2LS_DYNAMIC_CFG_H
#define CPROVER_2LS_2LS_DYNAMIC_CFG_H

#include <util/std_expr.h>
#include <util/graph.h>
#include <goto-programs/goto_program.h>

#include <ssa/ssa_unwinder.h>
#include <ssa/unwindable_local_ssa.h>
#include <solver/summary.h>


struct dynamic_cfg_edget
{
};

struct dynamic_cfg_idt
{
  goto_programt::const_targett pc;
  std::vector<unsigned> iteration_stack;
  // TODO: thread id

  std::string to_string() const
  {
    std::ostringstream sid;
    sid << i2string(pc->location_number);
    for(const auto &i : iteration_stack)
      sid << "." <<i2string(i);
    return sid.str();
  }
};

bool operator==(const dynamic_cfg_idt &a, const dynamic_cfg_idt &b);

struct dynamic_cfg_nodet:public graph_nodet<dynamic_cfg_edget>
{
  dynamic_cfg_idt id;
  bool is_loop_head;
  exprt assumption;
};

class dynamic_cfgt:public graph<dynamic_cfg_nodet>
{
public:
  inline dynamic_cfg_nodet& operator[](const dynamic_cfg_idt &id)
  {
    for(auto &n : nodes)
    {
      if(n.id==id)
        return n;
    }

    node_indext node=add_node();
    nodes[node].id=id;
    return nodes[node];
  }

  inline const nodet &operator[](node_indext n) const
  {
    return nodes[n];
  }

  // TODO: generalise this to non-inlined programs
  void operator()(
    const ssa_local_unwindert &ssa_unwinder,
    const unwindable_local_SSAt &ssa,
    const summaryt &summary);

protected:
  typedef std::pair<dynamic_cfg_idt, exprt> assumptiont;
  typedef std::vector<assumptiont> assumptionst;

  void build_cfg(
    const goto_programt &goto_program,
    const ssa_local_unwindert &ssa_unwinder);

  void build_from_invariants(
    const unwindable_local_SSAt &ssa,
    const exprt &invariants,
    assumptionst &assumptions);
  void build_from_invariant(
    const unwindable_local_SSAt &ssa,
    const exprt &invariant,
    assumptionst &assumptions);

  void add_assumptions(const assumptionst &assumptions);
};

#endif // CPROVER_2LS_SUMMARIZER_DYNAMIC_CFG_H
