/*******************************************************************\

Module: Conflict Analysis

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_CONFLICT_ANALYSIS_BASE_H
#define CPROVER_ACDL_CONFLICT_ANALYSIS_BASE_H

#include <util/graph.h>
#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "acdl_implication_graph.h"
#include "acdl_conflict_graph.h"
#include "../ssa/local_ssa.h"

class acdl_conflict_analysis_baset : public messaget
{
public: 
  
#if 0   
  acdl_decision_heuristics_condt &cond_heuristic;
  explicit acdl_conflict_analysis_baset(acdl_decision_heuristics_condt &_cond_heuristic) 
  :
  cond_heuristic(_cond_heuristic),
  backtrack_level(0),
  disable_backjumping(1)  
  {
  }
  
  virtual ~acdl_conflict_analysis_baset()
  {
  }
  
#endif

  explicit acdl_conflict_analysis_baset(acdl_domaint &_domain)
  :
  domain(_domain),
  backtrack_level(0),
  disable_backjumping(0)
  {}

  virtual ~acdl_conflict_analysis_baset()
  {
  }

  //property_checkert::resultt operator()(const local_SSAt &SSA, acdl_implication_grapht &graph, exprt &learned_clause);

  //Remark: the base class should not implement this function
  bool operator()(const local_SSAt &SSA, acdl_implication_grapht &graph, acdl_domaint::valuet &learned_clause);

  //Remark: all this stuff should go into a separate class derived from this base class
  unsigned int backtracks; 
  int backtrack_level;
  bool just_backtracked;
  bool disable_backjumping;
  void cancel_once(const local_SSAt &SSA, acdl_implication_grapht &graph, exprt& expr);
  void cancel_until(const local_SSAt &SSA, acdl_implication_grapht &graph, int lvl); 

protected: 
  acdl_domaint &domain;
  virtual void backtrack_to_level(acdl_implication_grapht &graph,unsigned int index);
  virtual void generalize_conflict(acdl_implication_grapht &graph) { assert(false); }

  void get_conflict_clause(const local_SSAt &SSA, acdl_implication_grapht &graph, acdl_domaint::valuet &clause);
  exprt flip(acdl_domaint::meet_irreduciblet &m); 
  bool chronological_backtrack(const local_SSAt &SSA, acdl_implication_grapht &graph);
  typedef acdl_domaint::valuet conflict_clauset;
  typedef std::vector<unsigned> clause_indicest;

};

#endif
