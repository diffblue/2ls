/*******************************************************************\

Module: Conflict Analysis

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_CONFLICT_ANALYSIS_H
#define CPROVER_ACDL_CONFLICT_ANALYSIS_H

#include <util/graph.h>
#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "acdl_implication_graph.h"
#include "../ssa/local_ssa.h"

class acdl_conflict_analysis_baset : public messaget
{
public: 
   
  explicit acdl_conflict_analysis_baset()
  {
  }

  virtual ~acdl_conflict_analysis_baset()
  {
  }

  virtual property_checkert::resultt operator()(
    acdl_implication_grapht &graph,
    exprt &learned_clause)
    { assert(false); }

protected:  
  virtual void backtrack_to_level(acdl_implication_grapht &graph,unsigned int index);
  virtual void generalize_conflict(acdl_implication_grapht &graph) { assert(false); }

};

#endif
