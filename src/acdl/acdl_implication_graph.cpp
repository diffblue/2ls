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
      nodes[nb].level = current_level;
#ifdef DEBUG
      assert(nb!=-1);
      assert(!has_edge(nb,na));
#endif
      add_edge(nb, na);
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

 Purpose: print graph output

 \*******************************************************************/
void acdl_implication_grapht::print_graph_output()
{
  //graph::output_dot(std::cout);
  output_graph(std::cout);
}

/*******************************************************************\

Function: acdl_implication_grapht::print_dot_output

  Inputs:

 Outputs:

 Purpose: print graph output

 \*******************************************************************/
    
void acdl_implication_grapht::output_graph(std::ostream &out) const 
{
  std::cout << "Printing Graph Output -- Total Nodes: " << nodes.size() << std::endl;
  for(node_indext i=0; i<nodes.size(); i++)
    output_graph_node(out, i);
}
    
/*******************************************************************\

Function: acdl_implication_grapht::print_dot_output

  Inputs:

 Outputs:

 Purpose: print graph output

 \*******************************************************************/
void acdl_implication_grapht::output_graph_node(std::ostream &out, node_indext n) const 
{
  
  const nodet &node=nodes[n];
  unsigned size = node.out.size();
  if(size == 0) {
    typename edgest::const_iterator ni = node.out.begin();
    node_indext ni_t = ni->first;
    out << n << " -> " << ni_t << '\n';
    out << nodes[n].expr << "@level :" << nodes[n].level << "#decision: " << nodes[n].is_decision <<  " -> " << nodes[ni_t].expr << "@level: " << nodes[ni_t].level << "#decision: " << nodes[ni_t].is_decision << '\n';
  }
  else {
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    out << n << " -> " << it->first << '\n';
    node_indext n1 = it->first;
    out << nodes[n].expr << "@level:" << nodes[n].level << "@decision:" << nodes[n].is_decision << " -> " << nodes[n1].expr << "@level:" << nodes[n1].level << "@decision:" << nodes[n1].is_decision << '\n';
  }
 }
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

/*******************************************************************\

Function: acdl_conflict_analysis_baset::remove_edges()

  Inputs:

 Outputs:

 Purpose: backtracks by one level

 \*******************************************************************/
void acdl_implication_grapht::remove_edges(node_indext n) 
{
  nodet &node=nodes[n];
  unsigned size = node.out.size();
  // base case
  if(size == 0) {
    typename edgest::const_iterator ni = node.out.begin();
    node_indext ni_t = ni->first;
    nodes[ni_t].erase_in(n);
    node.out.clear();
    return;
  }
  else {
  // delete all outgoing edges
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    nodes[it->first].erase_in(n);
    remove_edges(it->first);
  }
  node.out.clear();
  }
}
