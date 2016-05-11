/**************************************************\

Module: ACDL acdl_implication_graphtraph Dominator 

Author: Rajdeep Mukherjee, Peter Schrammel

\**************************************************/

#include "acdl_graph_dominator.h"

/*******************************************************************\

Function: graph_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

/*******************************************************************\

Function: graph_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

void acdl_graph_dominatort::fixedpoint(acdl_implication_grapht &graph)
{
  std::list<typename acdl_implication_grapht::node_indext> worklist;

  if(graph.size()==0)
    return;

  typename acdl_implication_grapht::nodet n = graph[supert::entry_node];  
  supert::dominators[supert::entry_node].insert(supert::entry_node);

  for(typename acdl_implication_grapht::edgest::const_iterator 
      s_it=(false?n.in:n.out).begin();
      s_it!=(false?n.in:n.out).end();
      ++s_it) {
    // check for marked graph.nodes only
    if(graph.nodes[s_it->first].marked && !graph.nodes[s_it->first].deleted)
    {
     worklist.push_back(s_it->first);
    }
  }

  while(!worklist.empty())
  {
    // get node from worklist
    typename acdl_implication_grapht::node_indext current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename acdl_implication_grapht::nodet &node=graph[current];
    if(supert::dominators[current].empty())
      for(typename acdl_implication_grapht::edgest::const_iterator 
          p_it=(false?node.out:node.in).begin();
          !changed && p_it!=(false?node.out:node.in).end();
          ++p_it)
        if(!supert::dominators[p_it->first].empty() && graph.nodes[p_it->first].marked)
        {
          supert::dominators[current]=supert::dominators[p_it->first];
          supert::dominators[current].insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(typename acdl_implication_grapht::edgest::const_iterator 
          p_it=(false?node.out:node.in).begin();
        p_it!=(false?node.out:node.in).end();
        ++p_it)
    {  
      //assert(supert::dominators[p_it->first].marked==true);
      const target_sett &other=supert::dominators[p_it->first];
      if(other.empty())
        continue;

      changed = set_intersect(supert::dominators[current],other,current)
	|| changed;
    }

    if(changed) // fixed point for node reached?
    {
      for(typename acdl_implication_grapht::edgest::const_iterator 
            s_it=(false?node.in:node.out).begin();
          s_it!=(false?node.in:node.out).end();
          ++s_it)
      {
        // check for marked graph.nodes only
        if(graph.nodes[s_it->first].marked && !graph.nodes[s_it->first].deleted)
        {
          worklist.push_back(s_it->first);
        }
      }
    }
  }
}

#if 0
  std::list<typename acdl_implication_grapht::node_indext> worklist;

  if(graph.size()==0)
    return;

  typename acdl_implication_grapht::nodet n = graph[entry_node];  
  dominators[entry_node].insert(entry_node);

  for(typename acdl_implication_grapht::edgest::const_iterator 
      s_it=(false?n.in:n.out).begin();
      s_it!=(false?n.in:n.out).end();
      ++s_it) {
    // check for marked graph.nodes only
    if(graph.nodes[s_it->first].marked && !G::nodes[s_it->first].deleted)
    {
     worklist.push_back(s_it->first);
    }
  }

  while(!worklist.empty())
  {
    // get node from worklist
    typename acdl_implication_grapht::node_indext current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename acdl_implication_grapht::nodet &node=graph[current];
    if(dominators[current].empty())
      for(typename acdl_implication_grapht::edgest::const_iterator 
          p_it=(false?node.out:node.in).begin();
          !changed && p_it!=(false?node.out:node.in).end();
          ++p_it)
        if(!dominators[p_it->first].empty() && graph.nodes[p_it->first].marked)
        {
          dominators[current]=dominators[p_it->first];
          dominators[current].insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(typename acdl_implication_grapht::edgest::const_iterator 
          p_it=(false?node.out:node.in).begin();
        p_it!=(false?node.out:node.in).end();
        ++p_it)
    {  
      assert(dominators[p_it->first].marked==true);
      const target_sett &other=dominators[p_it->first];
      if(other.empty())
        continue;

      changed = set_intersect(dominators[current],other,current)
	|| changed;
    }

    if(changed) // fixed point for node reached?
    {
      for(typename acdl_implication_grapht::edgest::const_iterator 
            s_it=(false?node.in:node.out).begin();
          s_it!=(false?node.in:node.out).end();
          ++s_it)
      {
        // check for marked graph.nodes only
        if(graph.nodes[s_it->first].marked && !graph.nodes[s_it->first].deleted)
        {
          worklist.push_back(s_it->first);
        }
      }
    }
  }
}
#endif
