/*******************************************************************\

Module: Conflict Analysis

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_ANALYZE_CONFLICT_BASE_H
#define CPROVER_2LS_ACDL_ACDL_ANALYZE_CONFLICT_BASE_H

#include <util/graph.h>
#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "acdl_conflict_graph.h"
#include "../ssa/local_ssa.h"

class acdl_analyze_conflict_baset : public messaget
{
protected:
  acdl_domaint &domain;

public:

  explicit acdl_analyze_conflict_baset(acdl_domaint &_domain)
    :
  domain(_domain),
    backtrack_level(0),
    disable_backjumping(0),
    conflicting_clause(-1),
    bcp_queue_top(0)
    {}

  virtual ~acdl_analyze_conflict_baset()
  {
  }

  bool operator()(const local_SSAt &SSA, acdl_conflict_grapht &graph);
  // Remark: all this stuff should go into a separate class derived from this base class
  unsigned int backtracks;
  int backtrack_level;
  bool just_backtracked;
  bool disable_backjumping;
  int conflicting_clause;
  unsigned bcp_queue_top;
  void cancel_once(const local_SSAt &SSA, acdl_conflict_grapht &graph);
  void cancel_until(const local_SSAt &SSA, acdl_conflict_grapht &graph, int lvl);
  void negate(exprt& exp, acdl_domaint::valuet &clause);
  void get_ai_reason(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &reason);
  void find_uip(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &conf_clause, unsigned dlevel);

  unsigned get_earliest_contradiction(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::meet_irreduciblet &exp);
  unsigned get_latest_contradiction(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::meet_irreduciblet &exp);
  int first_contradiction_on_trail(const exprt& expr, acdl_conflict_grapht &graph, int start, int end);
  enum proof_typet { PROPOSITIONAL, ABSINT };
  proof_typet last_proof;
  std::vector<acdl_domaint::valuet> learned_clauses;
  exprt flip(acdl_domaint::meet_irreduciblet &m);

protected:  
  virtual void generalize_conflict(acdl_conflict_grapht &graph) { assert(false); }

  void get_conflict_clause(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &clause);
  bool chronological_backtrack(const local_SSAt &SSA, acdl_conflict_grapht &graph);
  typedef acdl_domaint::valuet conflict_clauset;
  typedef std::vector<unsigned> clause_indicest;

};

#endif
