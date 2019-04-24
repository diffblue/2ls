/*******************************************************************\

Module: Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Summary

#ifndef CPROVER_2LS_SOLVER_SUMMARY_H
#define CPROVER_2LS_SOLVER_SUMMARY_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <ssa/local_ssa.h>

typedef enum {YES, NO, UNKNOWN} threevalt;

class summaryt
{
 public:
  typedef exprt predicatet;

  typedef std::list<symbol_exprt> var_listt;
  typedef std::set<symbol_exprt> var_sett;

  summaryt() :
    fw_precondition(nil_exprt()),
    fw_transformer(nil_exprt()),
    fw_invariant(nil_exprt()),
    bw_precondition(nil_exprt()),
    bw_postcondition(nil_exprt()),
    bw_transformer(nil_exprt()),
    bw_invariant(nil_exprt()),
    aux_precondition(nil_exprt()),
    termination_argument(nil_exprt()),
    terminates(UNKNOWN),
    mark_recompute(false) {}

  var_listt params;
  var_sett globals_in, globals_out;
  ssa_value_domaint value_domain_in, value_domain_out;
  predicatet fw_precondition; // accumulated calling contexts (over-approx)
  //  predicatet fw_postcondition; // we are not projecting that out currently
  predicatet fw_transformer; // forward summary (over-approx)
  predicatet fw_invariant; // forward invariant (over-approx)
  predicatet bw_precondition; // accumulated preconditions (over/under-approx)
  predicatet bw_postcondition; // accumulated postconditions (over/under-approx)
  predicatet bw_transformer; // backward summary (over- or under-approx)
  predicatet bw_invariant; // backward invariant (over- or under-approx)

  predicatet aux_precondition;

  predicatet termination_argument;
  threevalt terminates;

  bool mark_recompute; // to force recomputation of the summary
                       // (used for invariant reuse in k-induction)

  void output(std::ostream &out, const namespacet &ns) const;

  void join(const summaryt &new_summary);

  void set_value_domains(const local_SSAt &SSA);

 protected:
  void combine_or(exprt &olde, const exprt &newe);
  void combine_and(exprt &olde, const exprt &newe);
};

std::string threeval2string(threevalt v);

#endif
