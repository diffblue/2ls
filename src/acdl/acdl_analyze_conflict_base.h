/*******************************************************************\

Module: Conflict Analysis

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_CONFLICT_ANALYSIS_BASE_H
#define CPROVER_ACDL_CONFLICT_ANALYSIS_BASE_H

#include <util/graph.h>
#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "acdl_conflict_graph.h"
#include "../ssa/local_ssa.h"

class acdl_analyze_conflict_baset : public messaget
{
public: 
  
  explicit acdl_analyze_conflict_baset(acdl_domaint &_domain)
  :
  domain(_domain),
  backtrack_level(0),
  disable_backjumping(0),
  conflicting_clause(-1)
  {}

  virtual ~acdl_analyze_conflict_baset()
  {
  }

  bool operator()(const local_SSAt &SSA, acdl_conflict_grapht &graph); 
  //Remark: all this stuff should go into a separate class derived from this base class
  unsigned int backtracks; 
  int backtrack_level;
  int conflicting_clause;
  bool just_backtracked;
  bool disable_backjumping;
  void cancel_once(const local_SSAt &SSA, acdl_conflict_grapht &graph);
  void cancel_until(const local_SSAt &SSA, acdl_conflict_grapht &graph, int lvl); 
  void negate(exprt& exp, acdl_domaint::valuet &clause);
  void get_ai_reason(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &reason);
  void find_uip(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &conf_clause, unsigned dlevel);
  
  unsigned get_earliest_contradiction(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::meet_irreduciblet &exp);
  int unit_rule(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &clause);
  enum proof_typet { PROPOSITIONAL, ABSINT };
  proof_typet last_proof;    
  enum clause_statet { CONFLICT = 0, UNKNOWN = 1, SATISFIED = 2, UNIT = 3};
  clause_statet clause_state;
  std::vector<acdl_domaint::valuet> learned_clauses;
  
protected: 
  acdl_domaint &domain;
  virtual void generalize_conflict(acdl_conflict_grapht &graph) { assert(false); }

  void get_conflict_clause(const local_SSAt &SSA, acdl_conflict_grapht &graph, acdl_domaint::valuet &clause);
  exprt flip(acdl_domaint::meet_irreduciblet &m); 
  bool chronological_backtrack(const local_SSAt &SSA, acdl_conflict_grapht &graph);
  typedef acdl_domaint::valuet conflict_clauset;
  typedef std::vector<unsigned> clause_indicest;

};

#endif
