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

class acdl_solvert : public messaget
{
public:
  
  explicit acdl_solvert(const optionst &_options,
			acdl_domaint &_domain,
			acdl_decision_heuristicst &_decision_heuristics,
                        acdl_worklist_baset &_worklist)
    : 
    options(_options),
    domain(_domain),
    decision_heuristics(_decision_heuristics),
    worklist(_worklist)
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
    
  typedef std::list<acdl_domaint::statementt> assert_listt;
  
  typedef struct {
    typedef exprt nodet;
    typedef std::list<nodet> deduction_list;
    // root node is assumed nil_exprt()
    std::map<nodet, nodet> edges; //reverse edges,
                                  //i.e. e1 maps to e2 <=> directed edge (e2,e1)
    nodet current_node;
    int decision_level;
    std::map<nodet, acdl_domaint::valuet> backtrack_points;
    std::map<nodet, deduction_list> propagate_list;  // used to store list of deductions
  } decision_grapht; 
  
  property_checkert::resultt propagate(const local_SSAt &SSA,
				       acdl_domaint::valuet &v );

  void decide(const local_SSAt &SSA,
	      acdl_domaint::valuet &v,
	      decision_grapht &g,
	      assert_listt &alist);
  
  property_checkert::resultt analyze_conflict(const local_SSAt &SSA,
			acdl_domaint::valuet &v,
			decision_grapht &g);
};


#endif
 
