/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_DATA_FLOW_H
#define DELTACHECK_SSA_DATA_FLOW_H

#include <util/threeval.h>

#include "../ssa/local_ssa.h"
#include "../solver/fixed_point.h"

class ssa_fixed_pointt
{
public:
  typedef local_SSAt::locationt locationt;

  explicit ssa_fixed_pointt(
    const local_SSAt &_SSA_old,
    const local_SSAt &_SSA_new,
    const namespacet &_ns):
    SSA_old(_SSA_old),
    SSA_new(_SSA_new),
    ns(_ns),
    use_old(true),
    fixed_point(_ns)
  {
    compute_fixed_point();
  }

  explicit ssa_fixed_pointt(
    const local_SSAt &_SSA,
    const namespacet &_ns):
    SSA_old(_SSA),
    SSA_new(_SSA),
    ns(_ns),
    use_old(false),
    fixed_point(_ns)
  {
    compute_fixed_point();
  }

  inline void output(std::ostream &out) const
  {
    fixed_point.output(out);
  }
  
protected:
  const local_SSAt &SSA_old;
  const local_SSAt &SSA_new;
  const namespacet &ns;
  bool use_old;

public:
  fixed_pointt fixed_point;

protected:
  // fixed-point computation  
  void tie_inputs_together(std::list<exprt> &dest);
  void compute_fixed_point();
  bool iteration();
  void initialize_invariant();

  void do_backwards_edge(
    const local_SSAt &SSA, locationt loc);
  
  void do_backwards_edges();

  void countermodel_expr(
    const exprt &src,
    std::set<exprt> &dest);
};

#endif
