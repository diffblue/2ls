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
  // add a dummy node (node 0) when the graph is empty 
  // since the information of node 0 is obscured
  if(size() == 0) {
    node_indext n = graph::add_node();
    acdl_implication_graph_nodet &node = (*this)[n];
    node.expr = true_exprt();
    node.is_decision = false;
    node.level = 999;
    assert(nodes[n].out.size() == 0);
    assert(nodes[n].in.size() == 0);
  }

  for(std::vector<acdl_domaint::deductiont>::const_iterator it 
	= m_ir.begin(); it != m_ir.end(); it++)
  {
    //acdl_domaint::meet_irreduciblet exp = it->first; 
    int na = find_node(it->first);
    // new node, add to the graph
    if(na == -1)
    {
      na = graph::add_node();
      // new node can't be node 0
      assert(na != 0);
    }
    acdl_implication_graph_nodet &node = (*this)[na];
    node.expr = it->first;
    node.is_decision = false;
    node.level = current_level;
    node.deleted = false;
    
    // create all egdes pointing to this node 
    acdl_domaint::antecedentst ant = it->second;
    for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator 
	  it1 = ant.begin(); it1 != ant.end(); it1++)
    {
      node_indext nb = find_node(*it1);
      nodes[nb].level = current_level;
      nodes[nb].deleted = false;
      // valid node can't be node 0
      assert(nb != 0);
      std::cout << "[ADD DEDUCTIONS] " << nb << " -> " << na << std::endl;
      std::cout << "[ADD DEDUCTIONS] " << nodes[nb].expr << "@level :" << nodes[nb].level << "#decision: " << nodes[nb].is_decision <<  
      " -> " << nodes[na].expr << "@level: " << nodes[na].level << "#decision: " << nodes[na].is_decision << std::endl;
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
  node.deleted = false;
  current_level++;
  node.level = current_level;
  // add the decision to decision trail
  dec_trail.push_back(m_ir);
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
  for(node_indext i=1; i<size(); i++)
  {
    if(!nodes[i].deleted)
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

Function: acdl_implication_grapht::size()

  Inputs:

 Outputs:

 Purpose: find the size of the implication graph

 \*******************************************************************/
int acdl_implication_grapht::graph_size()
{
  int sizet=0;
  for(node_indext i=1; i<size(); i++)
  {
    if(nodes[i].deleted == 0)
     sizet++;
  }
  return sizet;
}

/*******************************************************************\

Function: acdl_implication_grapht::print_dot_output

  Inputs:

 Outputs:

 Purpose: print graph output

 \*******************************************************************/
    
void acdl_implication_grapht::output_graph(std::ostream &out) const 
{
  int sizet=0;
  for(node_indext i=1; i<size(); i++)
  {
    if(nodes[i].deleted == 0)
     sizet++;
  }
  std::cout << "Printing Graph Output -- Total Nodes: " << sizet << std::endl;

  for(node_indext i=1; i<size(); i++) {
    if(nodes[i].deleted==0)
    output_graph_node(out, i);
  }

 for(node_indext j=1; j<size(); j++)
 {
   if(nodes[j].deleted==0)
   std::cout << "Node number: " << j << "  Expression: " << (*this)[j].expr << 
   "  In edges: " << nodes[j].in.size() << "  Out edges: " << nodes[j].out.size() << std::endl;
 }
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
#if 0
  if(size == 0) {
    typename edgest::const_iterator ni = node.out.begin();
    node_indext ni_t = ni->first;
    out << "SIZE 0 " << n << " -> " << ni_t << '\n';
    out << nodes[n].expr << "@level :" << nodes[n].level << "#decision: " << nodes[n].is_decision <<  
    " -> " << nodes[ni_t].expr << "@level: " << nodes[ni_t].level << "#decision: " << nodes[ni_t].is_decision << '\n';
  }
#endif
//  else {
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    out << n << " -> " << it->first << '\n';
    node_indext n1 = it->first;
    out << nodes[n].expr << "@level:" << nodes[n].level << "@decision:" << nodes[n].is_decision << 
    " -> " << nodes[n1].expr << "@level:" << nodes[n1].level << "@decision:" << nodes[n1].is_decision << '\n';
  }
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    out << n << " -> " << it->first << '\n';
  }
// }
}
/*******************************************************************\

Function: acdl_implication_grapht::find_node

  Inputs:

 Outputs:

 Purpose: search all nodes to find the matching one

 \*******************************************************************/
acdl_implication_grapht::node_indext acdl_implication_grapht::find_node(const exprt &expr)
{
  for(node_indext i=1; i<size(); i++)
  {
      if((*this)[i].expr == expr && (!(*this)[i].deleted))
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
void acdl_implication_grapht::remove_out_edges(node_indext n) 
{
  nodet &node=nodes[n];
  unsigned size = node.out.size();
  // base case
  if(size == 0) {
    typename edgest::const_iterator ni = node.out.begin();
    node_indext ni_t = ni->first;
    nodes[ni_t].erase_in(n);
    node.out.clear();
    #if 0
    // special case for guard node in assertions
    if(nodes[ni_t].in.size() == 0) {
      std::cout << "guilty node :" << ni_t << std::endl;
      nodes[ni_t].erase_in(n);
      node.out.clear();
      //nodet &node_0 = nodes[ni_t];
      //node_0.in.clear();
    }
    return;
    #endif
  }
  else {
  // delete all outgoing edges
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    if(nodes[it->first].level == current_level && (!nodes[it->first].deleted)) {
      nodes[it->first].erase_in(n);
      std::cout << "Removing" << n << " -> " << it->first << std::endl; 
      remove_out_edges(it->first);
    }
  }
  node.out.clear();
  }
}


/*******************************************************************\

Function: acdl_conflict_analysis_baset::remove_edges()

  Inputs:

 Outputs:

 Purpose: remove in edges

 \*******************************************************************/
void acdl_implication_grapht::remove_in_edges(node_indext n) 
{
  nodet &node=nodes[n];
  unsigned size = node.in.size();
  // base case
  if(size == 0) {
    typename edgest::const_iterator ni = node.in.begin();
    node_indext ni_t = ni->first;
    nodes[ni_t].erase_out(n);
    node.in.clear();
    #if 0
    // special case for guard node in assertions
    if(nodes[ni_t].in.size() == 0) {
      std::cout << "guilty node :" << ni_t << std::endl;
      nodes[ni_t].erase_out(n);
      node.in.clear();
      //nodet &node_0 = nodes[ni_t];
      //node_0.out.clear();
    }
    return;
    #endif
  }
  else {
  // delete all outgoing edges
  for(typename edgest::const_iterator
      it=node.in.begin();
      it!=node.in.end();
      it++) {
    if(nodes[it->first].level == current_level && (!nodes[it->first].deleted)) {
      nodes[it->first].erase_out(n);
      std::cout << "Removing" << n << " -> " << it->first << std::endl; 
      remove_in_edges(it->first);
    }
  }
  node.in.clear();
  }
}

/*******************************************************************\

Function: acdl_implication_grapht::delete_node()

  Inputs:

 Outputs:

 Purpose: delete nodes of the implication graph

 \*******************************************************************/
void acdl_implication_grapht::delete_graph_nodes()
{
  for(node_indext i = 0; i < size(); i++) {    
    if(nodes[i].out.size() == 0 && nodes[i].in.size() == 0) {
     // remove the node 
     // nodes.erase(nodes.begin()+i);
     nodes[i].deleted = 1;
     std::cout << "Deleted graph node: " << nodes[i].expr << std::endl;   
    }
  }
}
