/*******************************************************************\

Module: Conflict Analysis

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_CONFLICT_ANALYSIS_H
#define CPROVER_ACDL_CONFLICT_ANALYSIS_H

#include <util/graph.h>
#include <goto-programs/property_checker.h>

#include "acdl_decision_heuristics_cond.h"
#include "acdl_domain.h"
#include "acdl_implication_graph.h"
#include "../ssa/local_ssa.h"

class acdl_conflict_analysis_baset : public messaget
{
public: 
  
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
#if 0   
  explicit acdl_conflict_analysis_baset()
  :
  backtrack_level(0)
  {}

  virtual ~acdl_conflict_analysis_baset()
  {
  }
#endif

  property_checkert::resultt operator()(acdl_implication_grapht &graph, exprt &learned_clause);
  unsigned int backtracks; 
  int backtrack_level;
  bool just_backtracked;
  bool disable_backjumping;
  void cancel_once(acdl_implication_grapht &graph);
protected: 
  virtual void backtrack_to_level(acdl_implication_grapht &graph,unsigned int index);
  virtual void generalize_conflict(acdl_implication_grapht &graph) { assert(false); }

  void get_conflict_clause(acdl_implication_grapht &graph, acdl_domaint::meet_irreduciblet &clause);
  exprt flip(acdl_domaint::meet_irreduciblet &m); 
  void chronological_backtrack(acdl_implication_grapht &graph);

};

#endif
