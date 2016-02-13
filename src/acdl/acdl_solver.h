/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_SOLVER_H
#define CPROVER_ACDL_SOLVER_H

#include <util/options.h>
#include <goto-programs/property_checker.h>

#include "../ssa/local_ssa.h"

#include "acdl_domain.h"
#include "acdl_decision_heuristics.h"
#include "acdl_worklist_base.h"
#include "acdl_conflict_analysis_base.h"

class acdl_solvert : public messaget
{
public:
  
  explicit acdl_solvert(const optionst &_options,
			acdl_domaint &_domain,
			acdl_decision_heuristicst &_decision_heuristics,
                        acdl_worklist_baset &_worklist,
                        acdl_conflict_analysis_baset &_conflict_analysis)
    : 
    options(_options),
    domain(_domain),
    decision_heuristics(_decision_heuristics),
    worklist(_worklist),
    conflict_analysis(_conflict_analysis)
    {
    }  

  ~acdl_solvert() 
    {
    }

  property_checkert::resultt operator()(const local_SSAt &SSA);

protected:
  const optionst &options;
  acdl_domaint &domain;
  acdl_decision_heuristicst &decision_heuristics;
  acdl_worklist_baset &worklist; 
  acdl_conflict_analysis_baset &conflict_analysis;
  acdl_implication_grapht implication_graph;
  std::vector<exprt> learned_clauses;
  
  property_checkert::resultt propagate(const local_SSAt &SSA);

  void decide(const local_SSAt &SSA);
  
  property_checkert::resultt analyze_conflict(const local_SSAt &SSA);
};


#endif
 
