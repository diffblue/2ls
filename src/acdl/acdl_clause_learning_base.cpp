/*******************************************************************\

Module: ACDL Clause Learning Base

Author: Rajdeep Mukherjee, Peter Schrammel

 \*******************************************************************/

#include <util/find_symbols.h>
#include "acdl_clause_learning_base.h"

/*******************************************************************\

Function: acdl_clause_learning_baset::

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_clause_learning_baset::add_deductions
  (const acdl_domaint::meet_irreduciblet &m_ir) {
 
  g.level = 0;
}
  
  
/*******************************************************************\

Function: acdl_clause_learning_baset::

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_clause_learning_baset::add_decisions
  (const acdl_domaint::meet_irreduciblet & m_ir) {
  
  g.level = 1;
}

/*******************************************************************\

Function: acdl_clause_learning_baset::

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_clause_learning_baset::backtrack_to_level(unsigned int idx) {
  g.level = idx;
}
