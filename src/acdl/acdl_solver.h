/*******************************************************************\

Module: ACDL Solver

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_SOLVER_H
#define CPROVER_ACDL_SOLVER_H

#include <util/options.h>
#include <util/find_symbols.h>
#include <goto-programs/property_checker.h>

#include "../ssa/local_ssa.h"

#include "acdl_domain.h"
#include "acdl_decision_heuristics_base.h"
#include "acdl_worklist_base.h"
#include "acdl_analyze_conflict_base.h"

class acdl_solvert : public messaget
{
public:
  
  explicit acdl_solvert(const optionst &_options,
      acdl_domaint &_domain,
      acdl_decision_heuristics_baset &_decision_heuristics,
      acdl_worklist_baset &_worklist,
      acdl_analyze_conflict_baset &_analyze_conflict)
    : 
      options(_options),
      domain(_domain),
      decision_heuristics(_decision_heuristics),
      worklist(_worklist),
      analyzes_conflict(_analyze_conflict),
      disable_generalization(0)
  {
  }  

  ~acdl_solvert() 
  {
  }

  property_checkert::resultt operator()(const local_SSAt &SSA,
					const exprt &assertion, const exprt &additional_constraint, const exprt &assumption);

  std::set<exprt> decision_variables;

protected:
  const optionst &options;
  acdl_domaint &domain;
  acdl_decision_heuristics_baset &decision_heuristics;
  acdl_worklist_baset &worklist; 
  acdl_analyze_conflict_baset &analyzes_conflict;
  std::vector<exprt> dec_not_in_trail;
  // collect all lhs cond variables from assumptions 
  // statements so that we do not make decisions on those
  std::string assume_lhs;
  // collect non-gamma-complete variables
  acdl_domaint::varst non_gamma_complete_var;
  // read-only-vars that appers in rhs of equalities
  acdl_domaint::varst read_only_vars;
  std::set<acdl_domaint::statementt> gamma_check_processed; 
  acdl_conflict_grapht conflict_graph;
  unsigned ITERATION_LIMIT=999999; 
  unsigned last_decision_index;  
  // global propagation module
  property_checkert::resultt propagate(const local_SSAt &SSA, const exprt& assertion);
  // propagation for chaotic iteration in Abstract interpretation proof
  property_checkert::resultt propagation(const local_SSAt &SSA, const exprt& assertion);
  // propagation for learned clauses only
  bool deduce(const local_SSAt &SSA);
  bool bcp(const local_SSAt &SSA, unsigned idx);

  bool decide(const local_SSAt &SSA, const exprt& assertion);
  acdl_domaint::varst value_to_vars(const acdl_domaint::valuet &value)
  {
    acdl_domaint::varst vars;
    for(acdl_domaint::valuet::const_iterator it = value.begin(); 
       it != value.end(); it++) {
      std::set<symbol_exprt> symbols;
      find_symbols(*it,symbols);
      for(std::set<symbol_exprt>::const_iterator 
        it1 = symbols.begin(); it1 != symbols.end(); ++it1) 
      vars.insert(*it1);
    }
    return vars;
  }

  unsigned decisions=0, learning=0, propagations=0, learned_literals=0; 
  std::set<symbol_exprt> all_vars;
  void init();
  bool analyze_conflict(const local_SSAt &SSA, const exprt& assertion);
  void generalize_proof(const local_SSAt &SSA, const exprt& assertion, acdl_domaint::valuet& val) const;

  bool disable_generalization;
  void initialize_decision_variables(acdl_domaint::valuet &val);
  void pre_process(const local_SSAt &SSA, const exprt &assertion, const exprt &assumption);
  void print_solver_statistics();
};


#endif
 
