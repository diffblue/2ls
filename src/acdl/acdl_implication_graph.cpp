/*******************************************************************\

Module: Implication graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include "acdl_implication_graph.h"
#include "acdl_graph_dominator.h"
# define DEBUG

/*******************************************************************\

Function: acdl_implication_grapht::add_deductions

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_implication_grapht::add_deductions
  (const local_SSAt &SSA, const acdl_domaint::deductionst &m_ir)
{
  // add a dummy node (node 0) when the graph is empty 
  // since the information of node 0 is obscured
  if(size() == 0) {
    node_indext n = graph::add_node();
    acdl_implication_graph_nodet &node = (*this)[n];
    node.expr = true_exprt();
    node.is_decision = false;
    //node.level = 999;
    node.deleted = true;
    node.dec_level.push_back(999);
    assert(nodes[n].out.size() == 0);
    assert(nodes[n].in.size() == 0);
  }

  for(std::vector<acdl_domaint::deductiont>::const_iterator it 
	= m_ir.begin(); it != m_ir.end(); it++)
  {
    //acdl_domaint::meet_irreduciblet exp = it->first; 
    int na = find_node(it->first);
    // new node, add to the graph
    // do not insert any cyclic deductions
    if(na == -1)
    {
      na = graph::add_node();
      // new node can't be node 0
      assert(na != 0);

      acdl_implication_graph_nodet &node = (*this)[na];
      node.expr = it->first;
      node.is_decision = false;
      //node.level = current_level;
      std::vector<int>::iterator itk;
      itk = find(node.dec_level.begin(), node.dec_level.end(), current_level);
      if(itk == node.dec_level.end())
        node.dec_level.push_back(current_level);
      node.deleted = false;

      // create all egdes pointing to this node 
      acdl_domaint::antecedentst ant = it->second;
      for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator 
          it1 = ant.begin(); it1 != ant.end(); it1++)
      {
        node_indext nb = find_node(*it1);
        //nodes[nb].level = current_level;
        std::vector<int>::iterator itl;
        itl = find(nodes[nb].dec_level.begin(), nodes[nb].dec_level.end(), current_level);
        if(itl == nodes[nb].dec_level.end())
          nodes[nb].dec_level.push_back(current_level);
        nodes[nb].deleted = false;
        // valid node can't be node 0
        assert(nb != 0);
        std::cout << "[ADD DEDUCTIONS] " << nb << " -> " << na << std::endl;
        std::cout << "[ADD DEDUCTIONS] " << from_expr(SSA.ns, "", nodes[nb].expr) << "@level :" << nodes[nb].dec_level.back() << "#decision: " << nodes[nb].is_decision <<  
          " -> " << from_expr(SSA.ns, "", nodes[na].expr) << "@level: " << nodes[na].dec_level.back() << "#decision: " << nodes[na].is_decision << std::endl;
#ifdef DEBUG
        assert(nb!=-1);
        assert(!has_edge(nb,na));
#endif
        // logic to determine deduction cycles of length 1
        //if(!has_edge(na, nb))
        add_edge(nb, na);
      }
    }
    else { 
      // only update the decision level of the consequent node
      // with the decision level of the current decision
      //nodes[na].level = current_level;
      std::vector<int>::iterator it2;
      it2 = find(nodes[na].dec_level.begin(), nodes[na].dec_level.end(), current_level);
      if(it2 == nodes[na].dec_level.end())
        nodes[na].dec_level.push_back(current_level);
      // set deleted flag to false
      nodes[na].deleted = false;
      continue;
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
  // add a dummy node (node 0) when the graph is empty 
  // since the information of node 0 is obscured
  if(size() == 0) {
    node_indext n = graph::add_node();
    acdl_implication_graph_nodet &node = (*this)[n];
    node.expr = true_exprt();
    node.is_decision = false;
    //node.level = 999;
    node.dec_level.push_back(999);
    assert(nodes[n].out.size() == 0);
    assert(nodes[n].in.size() == 0);
  }
  graph::node_indext n = graph::add_node();
  acdl_implication_graph_nodet &node = (*this)[n];
  node.expr = m_ir;
  node.is_decision = true;
  node.conflict = false;
  node.deleted = false;
  ++current_level;
  //node.level = current_level;
  std::vector<int>::iterator it;
  it = find(node.dec_level.begin(), node.dec_level.end(), current_level);
  if(it == node.dec_level.end())
    node.dec_level.push_back(current_level);
  // add the decision to decision trail
  dec_trail.push_back(m_ir);
}
 
/*******************************************************************\

Function: acdl_conflict_analysis_baset::check consistency()

  Inputs:

 Outputs:

 Purpose: check whether the graph is consistent after backtracking

 \*******************************************************************/
void acdl_implication_grapht::check_consistency(int lvl)
{
  std::cout << "*********************************************" << std::endl;
  std::cout << "Checking consistency of the implication graph" << std::endl;
  std::cout << "*********************************************" << std::endl;
  for(node_indext i = 1; i < size(); i++) {
    // all the nodes in graph must have level less or equal to the 
    // backtrack level, the nodes with level>lvl must be deleted
    if(!nodes[i].deleted) {
      assert(nodes[i].dec_level.back() <= lvl); 
      #if 0
      if(nodes[i].dec_level.back() > lvl) 
        std::cout << "ERROR nodes: " << "Node idx: " << i << " level: " << nodes[i].dec_level.back() 
        << "expr" << nodes[i].expr << std::endl;
      #endif
    }
  }
  std::cout << "The implication graph is consistent, Go ACDL !!" << std::endl;
}
/*******************************************************************\

 Function: acdl_implication_grapht::mark_node()

  Inputs:

  Outputs:

 Purpose: mark nodes of the implication graph starting from 
          the current decision node to the BOTTOM node using 
          forward reachability

 \*******************************************************************/
void acdl_implication_grapht::mark_node(node_indext start)
{
  nodet &node=nodes[start];
  unsigned size = node.out.size();
  // base case
  if(size == 0) {
   if(node.expr == false_exprt()) {
     assert(node.dec_level.back() == current_level);
     assert(node.deleted == false); 
     node.marked = true;
   }
  }
  else {
   for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    if(nodes[it->first].dec_level.back() == current_level 
             && (!nodes[it->first].deleted)) {
      mark_node(it->first);
      nodes[it->first].marked = true;
    }
   }
  }
}

/*******************************************************************\

unction: acdl_implication_grapht::first_uip

  Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/
acdl_implication_grapht::node_indext  acdl_implication_grapht::first_uip(const local_SSAt &SSA)
{
  std::cout << "******************" << std::endl;
  std::cout << "Computing the UIP" << std::endl;
  std::cout << "******************" << std::endl;
  acdl_domaint::meet_irreduciblet dec_expr =  dec_trail.back();
  node_indext na = find_node(dec_expr);
  assert(na >= 0);
  int nb = find_node(false_exprt());
  assert(nb >= 0);
  // the out edges of a false node is zero
  assert(nodes[nb].out.size() == 0);
  
  const nodet &node=nodes[na];
  assert(node.in.size() == 0);
  assert(node.is_decision == true);
  assert(node.dec_level.back() == current_level);
  //entry_node start;
  graph::node_indext entry_node=na;
  // call mark node
  //mark_node(na);  
  acdl_graph_dominatort dominator;
  dominator(*this, na);
  
  //int size = dominator.dominators.size();
  // print the dominator
  dominator.output(std::cout); 
  unsigned min_node_id = 0;
  unsigned max_node_id = 999999;
  bool first_uip_selected = false;
  //acdl_graph_dominatort::dominatorst::const_iterator uip;
  node_indext uip=-1;
  
#ifdef DEBUG
  std::cout << "The current level of conflict is: " << current_level << std::endl;
#endif
    
  // find the dominator that is the smallest and 
  // contains the false_node
  std::cout << "searching for uip" << std::endl;
  for(acdl_graph_dominatort::dominatorst::const_iterator it = dominator.dominators.begin();
      it != dominator.dominators.end(); ++it)
  {
    assert(nodes[it->first].deleted == false);
#ifdef DEBUG
    std::cout << "Checking UIP for the following node" << std::endl;
    std::cout << "node expr: " << from_expr(SSA.ns, "", nodes[it->first].expr) << " node id: " << it->first << " level: " << nodes[it->first].dec_level.back() << std::endl; 
#endif   
    // check the target list of a dominated node if the dominated 
    // node is at current level and the dominated node is a false_exprt
    if(nodes[it->first].dec_level.back() == current_level && nodes[it->first].expr == false_exprt()) {
#ifdef DEBUG
      std::cout << "Searching dominators of BOTTOM" << std::endl;
#endif
      for(acdl_graph_dominatort::target_sett::const_iterator d_it = it->second.begin();
         d_it!=it->second.end(); ++d_it)
      {
        assert(nodes[*d_it].deleted == false);
#ifdef DEBUG
        std::cout << "node expr: " << nodes[*d_it].expr << " node id: " << *d_it << " level: " << nodes[*d_it].dec_level.back() << std::endl; 
#endif
        // find dominator that dominates false exprt
        if((it->first != *d_it) && nodes[*d_it].dec_level.back() == current_level) {
#ifdef DEBUG
         std::cout << "found a dominator for BOTTOM node" << std::endl; 
#endif
         // finding the dominator that dominates 
         // largest number of nodes (this implicitly 
         // means finding dominator that is farthest 
         // from the false node -- last uip)
         if(!first_uip_selected) {
#ifdef DEBUG
           std::cout << "Searching for last uip" << std::endl;
#endif
           // ******* last uip ********
           if(*d_it < max_node_id) {
             max_node_id = *d_it; 
             // save the dominator 
             uip = *d_it;
           }
         }
         else if(first_uip_selected) {
#ifdef DEBUG
           std::cout << "Searching for first uip" << std::endl;
#endif
           // ******** first uip ********* 
           if(*d_it > min_node_id) {
             min_node_id = *d_it; 
             // save the dominator which 
             uip = *d_it;
           }
         }
        }
      }
    }
  }
  
  std::cout << "Found the UIP" << std::endl;
  
  // The UIP node must be a valid node in the graph
  // if not, then restart the uip search from the 
  // entry_node = false_exprt. This happens because 
  // the structure of deductions is such that the 
  // decision node (entry node for dominator) and the 
  // BOTTOM node leading to conflict can be disconnected
  assert(uip <= size());
  std::cout << "The uip node is: NODE(" << uip << ")" << " UIP EXPRESSION (" << from_expr(SSA.ns, "", nodes[uip].expr) << ")" << std::endl;
  
  // call unmark node
  // unmark(); 
  // check that the uip node is at current decision level
  const nodet &uip_node=nodes[uip];
  assert(uip_node.dec_level.back()==current_level);
  return uip;
}


/*******************************************************************\

Function: acdl_implication_grapht:get_reason

  Inputs:

 Outputs:

 Purpose: derive the reason

 \*******************************************************************/
void acdl_implication_grapht::get_reason
  (const local_SSAt &SSA, node_indext uip, acdl_domaint::valuet &reason)
{
  // collect all decision variables 
  // from the dec trail 
  std::cout << "inside reason 1" << std::endl;
  acdl_domaint::valuet dec_normalize;
  unsigned dec_size = dec_trail.size();
  int found = -1;
  for(unsigned j=0; j<dec_size; j++)
   std::cout << "The dec expr " << j << "is: " << dec_trail[j];
  
  for(unsigned i=0; i<dec_size; i++)
  {
     std::cout << "inside reason loop" << std::endl;
     acdl_domaint::meet_irreduciblet dec_exp = dec_trail[i];
     std::cout << "The dec expr " << i << "is: " << from_expr(SSA.ns, "", dec_exp);
     int n = find_node(dec_exp);
     
     // find if this node has been assigned before
     // in decision level less than current level
     // found = search_node__dec_level(n);
     // some decision nodes could be deleted
     // due to backtracking, hence the following check
     // if(n != -1) // && found != -1) 
     if(nodes[n].is_decision && n!= -1)
     {
      std::cout << "the node is decision node" << std::endl;
      std::cout << "The valid dec expr node " << n << "is: " << from_expr(SSA.ns, "", dec_exp);
      //assert(nodes[n].is_decision);
      dec_normalize.push_back(dec_trail[i]);
     }
  }
  
  std::cout << "outside reason loop" << std::endl;
  // normalize the decision 
  // acdl_domaint::normalize_val(dec_normalize);
  // iterate over all decision nodes and 
  // insert into reason 
  // reason = dec_normalize;
  reason.assign(dec_normalize.begin(), dec_normalize.end());
  //reason.push_back(nodes[dec_node].expr);
  
#if 0  
  // get the uip node
  nodet &node=nodes[uip];
  
  // container to store nodes that are
  // connected to uip through its out edges
  std::vector<node_indext> out_nodes;
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    out_nodes.push_back(it->first);
  }
  
  // iterate over all nodes "n" in the container "out_nodes"
  // and find the decision nodes that lead to "n"
  for(std::vector<node_indext>::iterator it = out_nodes.begin(); 
          it != out_nodes.end(); ++it) {
    // make sure that the decision node is not deleted 
    // and the level of the decision node is less than the current level
    // The last property guarantees asserting conflict clause
    if(!nodes[*it].deleted && nodes[*it].dec_level.back() < current_level) {
      node_indext dec_node = find_dec_node(*it);           
      assert(nodes[dec_node].is_decision==true);
      reason.push_back(nodes[dec_node].expr);
    }
  }
#endif  
}


/*******************************************************************\

Function: acdl_conflict_analysis_baset::search_node__dec_level()

  Inputs:

 Outputs:

 Purpose: search if a node has decision level equal to current level

 \*******************************************************************/
int acdl_implication_grapht::search_node__current_level(node_indext n) 
{
  for(unsigned i=0;i<nodes[n].dec_level.size();i++) {
    if(nodes[n].dec_level[i] == current_level) 
     return nodes[n].dec_level[i];   
  }
  return -1;
}
/*******************************************************************\

Function: acdl_conflict_analysis_baset::search_node__dec_level()

  Inputs:

 Outputs:

 Purpose: search if a node has decision level less than current level

 \*******************************************************************/
int acdl_implication_grapht::change_node__current_level(node_indext n) 
{
  int dec;
  for(unsigned i=0;i<nodes[n].dec_level.size();i++) {
    if(nodes[n].dec_level[i] == current_level) 
     dec = nodes[n].dec_level[i];   
     nodes[n].dec_level[i] == -1;
     return dec;
  }
  return -1;
}
/*******************************************************************\

Function: acdl_conflict_analysis_baset::search_node__dec_level()

  Inputs:

 Outputs:

 Purpose: search if a node has decision level less than current level

 \*******************************************************************/
int acdl_implication_grapht::search_node__dec_level(node_indext n) 
{
  for(unsigned i=0;i<nodes[n].dec_level.size();i++) {
    if(nodes[n].dec_level[i] < current_level) 
     return nodes[n].dec_level[i];   
  }
  return -1;
}

/*******************************************************************\

Function: acdl_conflict_analysis_baset::find_dec_node()

  Inputs:

 Outputs:

 Purpose: recursively find a decision node starting from a node
          by backward traversal

 \*******************************************************************/
acdl_implication_grapht::node_indext acdl_implication_grapht::find_dec_node(node_indext n) 
{
  nodet &node=nodes[n];
  unsigned size = node.in.size();
  // base case
  if(size == 0) {
    //typename edgest::const_iterator ni = node.in.begin();
    //node_indext ni_t = ni->first;
    if(!nodes[n].deleted) {
      assert(nodes[n].is_decision==true);
      return n;
    }
  }
  else {
   // delete all incoming edges
   for(typename edgest::const_iterator
      it=node.in.begin();
      it!=node.in.end();
      it++) {
     if(!nodes[it->first].deleted) {
      find_dec_node(it->first);
     }
   }
  }
}

/*******************************************************************\

Function: acdl_implication_grapht::unmark nodes

  Inputs:

 Outputs:

 Purpose: Unmark nodes in the implication graph

 \*******************************************************************/
void acdl_implication_grapht::unmark_nodes()
{
  for(node_indext i=1; i<size(); i++)
  {
    if(nodes[i].marked)
     nodes[i].marked=false;
  }
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
void acdl_implication_grapht::print_graph_output(const local_SSAt &SSA)
{
  //graph::output_dot(std::cout);
  output_graph(SSA, std::cout);
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
    
void acdl_implication_grapht::output_graph(const local_SSAt &SSA, std::ostream &out) const 
{
  int sizet=0,size_del=0;
  for(node_indext i=1; i<size(); i++)
  {
    if(nodes[i].deleted == 0)
     sizet++;
    else 
     size_del++;
  }
  std::cout << "Printing Graph Output -- Total Valid Nodes: " << sizet << ", " << 
  "Total deleted Nodes: " << size_del << std::endl;

  for(node_indext i=1; i<size(); i++) {
    if(nodes[i].deleted==0)
    output_graph_node(SSA, out, i);
  }

 for(node_indext j=1; j<size(); j++)
 {
   //if(nodes[j].deleted==0)
     std::cout << "Node number: " << j << "  Expression: " << from_expr(SSA.ns, "", nodes[j].expr) << 
   "  In edges: " << nodes[j].in.size() << "  Out edges: " << nodes[j].out.size() << " Decision: "<< nodes[j].is_decision << " Deleted: " << nodes[j].deleted << " Marked: " << nodes[j].marked << "  DL vector: "; 
   for(int k=0;k<nodes[j].dec_level.size();k++)
     std::cout <<  nodes[j].dec_level[k] << "   ";
   std::cout << std::endl;
 }
}
    
/*******************************************************************\

Function: acdl_implication_grapht::print_dot_output

  Inputs:

 Outputs:

 Purpose: print graph output

 \*******************************************************************/
void acdl_implication_grapht::output_graph_node(const local_SSAt &SSA, std::ostream &out, node_indext n) const 
{
  
  const nodet &node=nodes[n];
  //unsigned size = node.out.size();
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
    if(!nodes[it->first].deleted) {
      out << n << " -> " << it->first << '\n';
      node_indext n1 = it->first;
      // assert that the consequent of a deduction can not be a decision node
      assert(!nodes[n1].is_decision);
      std::cout << from_expr(SSA.ns, "", nodes[n].expr) << "  @level:" << nodes[n].dec_level.back() << " @decision:" << nodes[n].is_decision << 
      " -> " << from_expr(SSA.ns, "", nodes[n1].expr) << " @level:" << nodes[n1].dec_level.back() << " @decision:" << nodes[n1].is_decision << '\n';
    }
  }
  /*for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
    out << n << " -> " << it->first << '\n';
  }*/
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

Function: acdl_conflict_analysis_baset::remove_out_edges()

  Inputs:

 Outputs:

 Purpose: remove the out edges starting from a given node

 \*******************************************************************/
void acdl_implication_grapht::remove_out_edges(node_indext n) 
{
  nodet &node=nodes[n];
  unsigned size = node.out.size();
  /*if(node.dec_level.back() == current_level) {
    node.dec_level.pop_back();
    // if the dec_level vector size of a 
    // node is zero, then assign decision level as -1 
    if(node.dec_level.size() == 0)
      node.dec_level.push_back(-1);
  }*/
  
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
      //std::cout << "Out Checking" << n << " -> " << it->first << std::endl; 
    if(nodes[it->first].dec_level.back() == current_level && (!nodes[it->first].deleted)) {
      nodes[it->first].erase_in(n);
      //std::cout << "Removing" << n << " -> " << it->first << std::endl; 
      std::cout << n << " -> " << it->first << std::endl; 
      remove_out_edges(it->first);
    }
  }
  node.out.clear();
  }
}


/*******************************************************************\

Function: acdl_conflict_analysis_baset::delete_nodes()

  Inputs:

 Outputs:

 Purpose: delete nodes in graph recursively

 \*******************************************************************/
void acdl_implication_grapht::delete_in_nodes(node_indext n) 
{
  
  //std::cout << "Checking the node: " << n << std::endl; 
  nodet &node=nodes[n];
  unsigned size = node.in.size();
  nodes[n].marked = true;
  // base case
  if(size == 0) {
    typename edgest::const_iterator ni = node.in.begin();
    node_indext ni_t = ni->first;
    nodes[ni_t].marked = true;
    //std::cout << "Removing Base case" << n << " <- " << ni_t << std::endl; 
    std::cout << n << " <- " << ni_t << std::endl; 
  }
  else {
  // delete all incoming edges
  for(typename edgest::const_iterator
      it=node.in.begin();
      it!=node.in.end();
      it++) {
      //std::cout << "Checking In" << n << " <- " << it->first << std::endl; 
    if(nodes[it->first].dec_level.back() == current_level) {
    //if(search_node__current_level(it->first) == current_level) {
      //std::cout << "Removing In" << n << " <- " << it->first << std::endl; 
      std::cout << n << " <- " << it->first << std::endl; 
      delete_in_nodes(it->first);
    }
   }
  }
}
  
  
/*******************************************************************\

Function: acdl_conflict_analysis_baset::delete_out_nodes()

  Inputs:

 Outputs:

 Purpose: delete nodes in graph recursively

 \*******************************************************************/
void acdl_implication_grapht::delete_out_nodes(node_indext n) 
{
  //std::cout << "Checking the node: " << n << std::endl; 
  nodet &node=nodes[n];
  unsigned size = node.out.size();
  nodes[n].marked = true;
  // base case
  if(size == 0) {
    typename edgest::const_iterator ni = node.out.begin();
    node_indext ni_t = ni->first;
    nodes[ni_t].marked = true;
    //std::cout << "Removing Base case" << n << " -> " << ni_t << std::endl; 
    std::cout << n << " -> " << ni_t << std::endl; 
  }
  else {
  // delete all outgoing edges
  for(typename edgest::const_iterator
      it=node.out.begin();
      it!=node.out.end();
      it++) {
      //std::cout << "Checking Out" << n << " -> " << it->first << std::endl; 
    if(nodes[it->first].dec_level.back() == current_level) {
    //if(search_node__current_level(it->first) == current_level) {
      //std::cout << "Removing Out" << n << " -> " << it->first << std::endl; 
      std::cout << n << " -> " << it->first << std::endl; 
      delete_out_nodes(it->first);
    }
   }
  }
}

/*******************************************************************\

Function: acdl_conflict_analysis_baset::remove_in_edges()

  Inputs:

 Outputs:

 Purpose: remove in edges

 \*******************************************************************/
void acdl_implication_grapht::remove_in_edges(node_indext n) 
{
  nodet &node=nodes[n];
  unsigned size = node.in.size();
  /*if(node.dec_level.back() == current_level) {
    node.dec_level.pop_back();
    // if the dec_level vector size of a 
    // node is zero, then assign decision level as -1 
    if(node.dec_level.size() == 0)
      node.dec_level.push_back(-1);
  }*/
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
  // delete all incoming edges
  for(typename edgest::const_iterator
      it=node.in.begin();
      it!=node.in.end();
      it++) {
      std::cout << "Checking" << n << " <- " << it->first << std::endl; 
    if(nodes[it->first].dec_level.back() == current_level && (!nodes[it->first].deleted)) {
      nodes[it->first].erase_out(n);
      std::cout << "Removing" << n << " <- " << it->first << std::endl; 
      remove_in_edges(it->first);
      /*node.dec_level.pop_back();
      // if the dec_level vector size of a 
      // node is zero, then assign decision level as -1 
      if(node.dec_level.size() == 0)
        node.dec_level.push_back(-1);*/
    }
  }
  node.in.clear();
  }
}


/*******************************************************************\

Function: acdl_implication_grapht::delete_node()

  Inputs:

 Outputs:

 Purpose: adjust decision level vector of a node in implication graph

 \*******************************************************************/
void acdl_implication_grapht::adjust_decision_level()
{
  bool found = 0;
  std::cout << "The current level is: " << current_level << "graph size is" << size() << std::endl;
  for(node_indext i=1; i<size(); i++) {    
     found = search_node__current_level(i); 
     if(found != -1) { 
       int dec = search_node__current_level(i);
       std::cout << "printing the marked node at current level" << nodes[i].expr << std::endl;
     }
  }
  
  for(node_indext i=1; i<size(); i++) {    
    if(nodes[i].dec_level.size() > 0) {
      if(nodes[i].marked && nodes[i].dec_level.back() == current_level) { 
        nodes[i].dec_level.pop_back();
      }
    }
  }
  for(node_indext j=1; j<size(); j++) {    
    // special case
    // there may be nodes in the graph which may not be 
    // marked because these nodes are unreachable from 
    // decision node or false exprt, mark the node here

    if(nodes[j].dec_level.size() > 0) {
      if(nodes[j].dec_level.back() == current_level && !nodes[j].marked) {
        std::cout << "special case node !! Node index: " << j << std::endl; 
        nodes[j].dec_level.pop_back();
        nodes[j].marked = true;
      }
    }
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
  for(node_indext i=1; i<size(); i++) {    
    // the condition below is OR because there are deductions
    // which may not be reachable from decision node or false_exprt
    // in which case they may not be marked, so the only way to identify
    // these nodes is by checking the decision level of these nodes
    if(nodes[i].dec_level.size() > 0) {
      if(nodes[i].dec_level.back() == current_level || nodes[i].marked) { 
        //if(search_node__current_level(i) == current_level || nodes[i].marked) {
        nodes[i].dec_level.pop_back();
        // if the dec_level vector size of a 
        // node is zero, then delete the node 
        if(nodes[i].dec_level.size() == 0) {
          nodes[i].deleted = 1;
          std::cout << "Deleted graph node: " << nodes[i].expr << std::endl;   
        }
       }
      }
      else {
        if(nodes[i].dec_level.size() == 0) {
          nodes[i].deleted = 1;
          std::cout << "Deleted graph node: " << nodes[i].expr << std::endl;   
        }
      }
  }
#if 0
     // check if the out edges and in edges are zero 
     // or the decision level is set -1 
     if((nodes[i].out.size() == 0 && nodes[i].in.size() == 0) || 
         (nodes[i].dec_level.back() == -1)) 
       // && nodes[i].dec_level.back() == current_level) 
     {
       // remove the node 
       nodes[i].deleted = 1;
       std::cout << "Deleted graph node: " << nodes[i].expr << std::endl;   
     }
  }
#endif  
}

/*******************************************************************\

Function: acdl_implication_grapht::find_node_expr

  Inputs:

 Outputs:

 Purpose: search all nodes to find the matching one

 \*******************************************************************/
exprt acdl_implication_grapht::find_node_expr(node_indext n) 
{
  assert(!nodes[n].deleted);
  return nodes[n].expr;
}

/*******************************************************************\

Function: acdl_implication_grapht::decision_level()

  Inputs:

 Outputs:

 Purpose: return decision level of current node

 \*******************************************************************/
int acdl_implication_grapht::decision_level(node_indext n) 
{
  assert(!nodes[n].deleted);
  return nodes[n].dec_level.back();
}
