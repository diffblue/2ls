/*******************************************************************\

Module: ACDL Clause Learning Base

Author: Rajdeep Mukherjee, Peter Schrammel

 \*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_conflict_analysis_base.h"

/*******************************************************************\

Function: acdl_conflict_analysis_baset::backtrack_to_level

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_analysis_baset::backtrack_to_level(acdl_implication_grapht &graph,
						      unsigned int idx)
{
  
}
  
/*******************************************************************\

Function: acdl_conflict_analysis_baset::operator()

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
  
  
property_checkert::resultt acdl_conflict_analysis_baset::operator()(acdl_implication_grapht &graph, exprt &learned_clause)
{ 
  if(graph.current_level == 0) {
    backtrack_level = -1;
    property_checkert::resultt result = property_checkert::PASS;
    return result;
  }
  else 
  {
    assert(false);
  }
}
