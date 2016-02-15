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
     acdl_implication_graph_nodet node;
     node.expr = it->first;
     node.is_decision = false;
     node.level = current_level;
     int na = search_node(node);
     // new node, add to the graph
     if(na == -1) {
       na = graph::add_node();
       node_info.first = na;
       node_info.second = node;
       // insert into graph nodes
       nodes.push_back(node_info);
     }  
     // create all egdes pointing to this node 
     acdl_domaint::antecedentst ant = it->second;
     for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator 
      it1 = ant.begin(); it1 != ant.end(); it1++) {
        acdl_implication_graph_nodet ant_node;
        ant_node.expr = *it1;
        ant_node.is_decision = false;
        ant_node.conflict = false;
        ant_node.level = current_level;
        int nb = search_node(ant_node);
        // must already exist in the graph
        assert(nb != -1);
        if(!has_edge(na,nb))
          graph::add_edge(na, nb);
      }
    }
   
#if 0  
  // create a node for each new meet irreducibles
  for(std::vector<acdl_domaint::deductiont>::const_iterator it 
    = m_ir.begin(); it != m_ir.end(); it++)
  {  
    acdl_implication_graph_nodet node;
    node.expr = it->first;
    node.is_decision = false;
    node.level = current_level;
    acdl_domaint::antecedentst ant = it->second;
    graph::node_indext na = graph::add_node();
    // check for conflicting node
    if(it->first == false_exprt()) 
      node.conflict = true;
    
    // insert into graph nodes
    nodes.push_back(node);
    // create a node for each antecedents which are 
    // used to infer the new meet irreducible
    for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator 
      it1 = ant.begin(); it1 != ant.end(); it1++) {
       acdl_implication_graph_nodet ant_node;
       ant_node.expr = *it1;
       ant_node.is_decision = false;
       ant_node.conflict = false;
       ant_node.level = current_level;
       // insert into graph nodes
       nodes.push_back(node);
       graph::node_indext nb = graph::add_node();
       graph::add_edge(na, nb);
    }
  }
#endif  
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
  node.conflict = false;
  node.level = current_level+1;
  current_level = current_level+1;
  graph::node_indext n = graph::add_node();
  node_info.first = n;
  node_info.second = node;
  // insert into graph nodes
  nodes.push_back(node_info);
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
  for(nodest::const_iterator it = nodes.begin(); it != nodes.end(); ++it) 
    value.push_back(it->second.expr);
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

Function: acdl_implication_grapht::search_node

  Inputs:

 Outputs:

 Purpose: search all nodes to find the matching one

 \*******************************************************************/
int acdl_implication_grapht::search_node(acdl_implication_graph_nodet &node)
{
  for(nodest::const_iterator itx = 
    nodes.begin(); itx != nodes.end(); ++itx) {
     exprt expr = itx->second.expr;
     if(expr == node.expr)
      return itx->first;
  }
  return -1;
}
