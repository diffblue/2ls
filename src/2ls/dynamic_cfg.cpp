/*******************************************************************\

Module: Dynamic Control Flow Graph

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Dynamic Control Flow Graph

#include <iostream>

#include "dynamic_cfg.h"

#include <domains/util.h>

/// generates the dynamic CFG
void dynamic_cfgt::operator()(
  const ssa_local_unwindert &ssa_unwinder,
  const unwindable_local_SSAt &ssa,
  const summaryt &summary)
{
  const goto_programt &goto_program=ssa.goto_function.body;
  build_cfg(goto_program, ssa_unwinder);

  assumptionst assumptions;
  build_from_invariants(ssa, summary.fw_invariant, assumptions);
  add_assumptions(assumptions);
}

bool operator==(const dynamic_cfg_idt &a, const dynamic_cfg_idt &b)
{
  return a.pc==b.pc && a.iteration_stack==b.iteration_stack;
}

/// annotates the nodes with assumptions
void dynamic_cfgt::add_assumptions(const assumptionst &assumptions)
{
  for(const auto &a : assumptions)
  {
    (*this)[a.first].assumption=a.second;
  }
}

/// extracts assumptions from invariants
void dynamic_cfgt::build_cfg(
  const goto_programt &goto_program,
  const ssa_local_unwindert &ssa_unwinder)
{
  std::vector<unsigned> iteration_stack;
  std::vector<node_indext> loop_node_stack;
  std::vector<unsigned> max_iteration_stack;
  std::map<goto_programt::const_targett,
           std::set<node_indext> > incoming_edges;

  forall_goto_program_instructions(it, goto_program)
  {
    node_indext node=add_node();
    nodes[node].id.pc=it;
    nodes[node].id.iteration_stack=iteration_stack;
    nodes[node].is_loop_head=false;
    nodes[node].assumption=nil_exprt();

    // this is the end of a loop
    //   (sink self-loops are translated into assume false in the SSA)
    if(it->is_backwards_goto() &&
       it->get_target()!=it)
    {
#if 0
      // Sanity checks
      const ssa_local_unwindert::loopt *loop=nullptr;
      if(!ssa_unwinder.find_loop(it->get_target()->location_number, loop))
      {
        std::cout << "NON-LOOP BACKEDGE? " << it->location_number
                  << " --> " << it->get_target()->location_number << std::endl;
        assert(false);
      }
      assert(!iteration_stack.empty());
      assert(!max_iteration_stack.empty());
#endif

      // max_unwind reached
      if(iteration_stack.back()==max_iteration_stack.back())
      {
        iteration_stack.pop_back();
        max_iteration_stack.pop_back();

        // add back-edge
        add_edge(node, loop_node_stack.back());

        loop_node_stack.pop_back();
      }
      // max_unwind not reached
      else
      {
        // add edges for end of loop
        const std::set<node_indext> &iedges=incoming_edges[it];
        for(const auto &from : iedges)
          add_edge(from, node);
        incoming_edges.erase(it);

        // jump back to loop head
        it=it->get_target();
        iteration_stack.back()++;
        node_indext new_node=add_node();
        nodes[new_node].id.iteration_stack=iteration_stack;
        nodes[new_node].id.pc=it;
        nodes[new_node].is_loop_head=false;
        nodes[new_node].assumption=nil_exprt();

        // add forward edge to unwound loop head
        add_edge(node, new_node);

        // remember forward gotos
        if(it->is_goto() && !it->is_backwards_goto())
          incoming_edges[it->get_target()].insert(new_node);
        goto_programt::const_targett next=it; ++next;
        if(next!=goto_program.instructions.end() &&
           (!it->is_goto() || !it->guard.is_true()))
          incoming_edges[next].insert(new_node);

        continue;
      }
    }
    // reconstruct sink self-loops
    else if(it->is_backwards_goto() &&
            it->get_target()==it)
    {
      nodes[node].is_loop_head=true;
      add_edge(node, node);
      continue;
    }

    // remember forward gotos
    if(it->is_goto() && !it->is_backwards_goto())
      incoming_edges[it->get_target()].insert(node);
    goto_programt::const_targett next=it; ++next;
    if(next!=goto_program.instructions.end() &&
       (!it->is_goto() || !it->guard.is_true()))
      incoming_edges[next].insert(node);

    // this is a loop head
    const ssa_local_unwindert::loopt *loop=nullptr;
    if(ssa_unwinder.find_loop(it->location_number, loop))
    {
      iteration_stack.push_back(0);
      loop_node_stack.push_back(node);
      assert(loop->current_unwinding>=0);
      max_iteration_stack.push_back(loop->current_unwinding);
      nodes[node].id.iteration_stack=iteration_stack;
      nodes[node].is_loop_head=true;
    }
    else
    {
      // alternative loop head detection when unwinder was not used
      for(const auto &incoming : it->incoming_edges)
      {
        if(incoming->is_backwards_goto() &&
           incoming!=it)
        {
          iteration_stack.push_back(0);
          loop_node_stack.push_back(node);
          max_iteration_stack.push_back(0);
          nodes[node].id.iteration_stack=iteration_stack;
          nodes[node].is_loop_head=true;
          break;
        }
      }
    }

    const std::set<node_indext> &iedges=incoming_edges[it];
    for(const auto &from : iedges)
      add_edge(from, node);
    incoming_edges.erase(it);
  }
}

/// extracts assumption from invariant
void dynamic_cfgt::build_from_invariant(
  const unwindable_local_SSAt &ssa,
  const exprt &invariant,
  assumptionst &assumptions)
{
  dynamic_cfg_idt id;
  if(invariant.op0().id()==ID_symbol)
    ssa.get_full_ssa_name(
      to_symbol_expr(invariant.op0()),
      id.pc,
      id.iteration_stack);
  else if(invariant.op0().id()==ID_and &&
          invariant.op0().op0().id()==ID_symbol)
    ssa.get_full_ssa_name(
      to_symbol_expr(invariant.op0().op0()),
      id.pc,
      id.iteration_stack);
  else
    assert(false);

  for(auto &a : assumptions)
  {
    // update existing
    if(a.first==id)
    {
      exprt::operandst e;
      if(a.second.id()==ID_and)
        e=a.second.operands();
      else
        e.push_back(a.second);

      exprt cexpr=invariant.op1(); // copy
      clean_expr(cexpr);
      e.push_back(cexpr);
      a.second=conjunction(e);
      return;
    }
  }

  // create new
  assumptions.push_back(assumptiont());
  assumptions.back().first=id;
  assumptions.back().second=invariant.op1(); // copy
  clean_expr(assumptions.back().second);
}

/// extracts assumptions from invariants
void dynamic_cfgt::build_from_invariants(
  const unwindable_local_SSAt &ssa,
  const exprt &invariants,
  assumptionst &assumptions)
{
  if(invariants.is_nil() || invariants.is_true())
    return;

  // expected format /\_i g_i=> inv_i
  if(invariants.id()==ID_implies)
  {
    build_from_invariant(ssa, invariants, assumptions);
  }
  else if(invariants.id()==ID_and)
  {
    forall_operands(it, invariants)
      build_from_invariants(ssa, *it, assumptions);
  }
}
