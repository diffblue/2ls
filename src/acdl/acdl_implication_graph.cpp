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
  for(std::vector<acdl_domaint::deductiont>::const_iterator it 
	= m_ir.begin(); it != m_ir.end(); it++)
  {
    //acdl_domaint::meet_irreduciblet exp = it->first; 
    int na = find_node(it->first);
    // new node, add to the graph
    if(na == -1)
    {
      na = graph::add_node();
    }
    acdl_implication_graph_nodet &node = (*this)[na];
    node.expr = it->first;
    node.is_decision = false;
    node.level = current_level;
    
    // create all egdes pointing to this node 
    acdl_domaint::antecedentst ant = it->second;
    for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator 
	  it1 = ant.begin(); it1 != ant.end(); it1++)
    {
      node_indext nb = find_node(*it1);
#ifdef DEBUG
      assert(nb!=-1);
      assert(!has_edge(na,nb));
#endif
      add_edge(na, nb);
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
  graph::node_indext n = graph::add_node();
  acdl_implication_graph_nodet &node = (*this)[n];
  node.expr = m_ir;
  node.is_decision = true;
  node.conflict = false;
  current_level++;
  node.level = current_level;
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
  for(node_indext i=0; i<size(); i++)
  {
    value.push_back(nodes[i].expr);
  }
}


/*******************************************************************\

Function: acdl_implication_grapht::print_dot_output

  Inputs:

 Outputs:

 Purpose: flatten all node expressions into a vector

 \*******************************************************************/
void acdl_implication_grapht::print_dot_output()
{
  graph::output_dot(std::cout);
}
    
    

/*******************************************************************\

Function: acdl_implication_grapht::find_node

  Inputs:

 Outputs:

 Purpose: search all nodes to find the matching one

 \*******************************************************************/
acdl_implication_grapht::node_indext acdl_implication_grapht::find_node(const exprt &expr)
{
  for(node_indext i=0; i<size(); i++)
  {
      if((*this)[i].expr == expr)
      return i;
  }
  return -1;
}
