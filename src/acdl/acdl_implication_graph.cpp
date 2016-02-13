/*******************************************************************\

Module: Implication graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include "acdl_implication_graph.h"

/*******************************************************************\

Function: acdl_implication_grapht::add_deductions

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_implication_grapht::add_deductions
  (const acdl_domaint::deductionst &m_ir)
{
  nodest deduce_node;
  // create a node for each new meet irreducibles
  for(std::vector<acdl_domaint::deductiont>::const_iterator it 
    = m_ir.begin(); it != m_ir.end(); it++)
  {  
    acdl_implication_graph_nodet node;
    node.expr = it->first;
    node.is_decision = false;
    node.level = current_level + 1;
    current_level = current_level + 1;
    acdl_domaint::antecedentst ant = it->second;
    deduce_node.push_back(node);
    
    // create a node for each antecedents which are 
    // used to infer the new meet irreducible
    for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator 
      it1 = ant.begin(); it1 != ant.end(); it1++) {
      acdl_implication_graph_nodet ant_node;
      ant_node.expr = *it1;
      ant_node.is_decision = false;
      ant_node.level = current_level + 1;
      current_level = current_level + 1;
      deduce_node.push_back(ant_node);
    }
  }
}

/*******************************************************************\

Function: acdl_implication_grapht::add_decision

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_implication_grapht::add_decision
  (const acdl_domaint::meet_irreduciblet & m_ir)
{
  acdl_implication_graph_nodet node;
  node.expr = m_ir;
  node.is_decision = true;
  node.level = current_level+1;
  current_level = current_level + 1;
  nodest decide_node;
  decide_node.push_back(node);
}
 

/*******************************************************************\

Function: acdl_implication_grapht::first_uip

  Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/
void acdl_implication_grapht::first_uip(nodest &cut)
{
  assert(false);
}

/*******************************************************************\

Function: acdl_implication_grapht::to_value

  Inputs:

 Outputs:

 Purpose: flatten all node expressions into a vector

 \*******************************************************************/
void acdl_implication_grapht::to_value
  (acdl_domaint::valuet &value) const
{
}
