/**************************************************\

Module: ACDL Graph Dominator 

Author: Rajdeep Mukherjee, Peter Schrammel

\**************************************************/

#include "acdl_graph_dominator.h"


/*******************************************************************\

Function: operator ()

  Inputs:

 Outputs:

 Purpose: Compute dominators

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::operator()(G &graph, typename G::node_indext _entry_node)
{
  entry_node = _entry_node;
  initialise(graph);
  fixedpoint(graph);
}


/*******************************************************************\

Function: graph_dominators_templatet::initialise

  Inputs:

 Outputs:

 Purpose: Initialises the elements of the fixed point analysis

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::initialise(G &graph)
{
  dominators.clear();
}

/*******************************************************************\

Function: graph_dominators_templatet::fixedpoint

  Inputs:

 Outputs:

 Purpose: Computes the MOP for the dominator analysis

\*******************************************************************/

template <class G, bool post_dom>
void graph_dominators_templatet<G, post_dom>::fixedpoint(G &graph)
{
  std::list<typename G::node_indext> worklist;

  if(graph.size()==0)
    return;

  typename G::nodet n = graph[entry_node];  
  dominators[entry_node].insert(entry_node);

  for(typename G::edgest::const_iterator 
      s_it=(post_dom?n.in:n.out).begin();
      s_it!=(post_dom?n.in:n.out).end();
      ++s_it) {
    // check for marked G::nodes only
    if(G::nodes[s_it->first].marked && !G::nodes[s_it->first].deleted)
    {
     worklist.push_back(s_it->first);
    }
  }

  while(!worklist.empty())
  {
    // get node from worklist
    typename G::node_indext current=worklist.front();
    worklist.pop_front();

    bool changed=false;
    typename G::nodet &node=graph[current];
    if(dominators[current].empty())
      for(typename G::edgest::const_iterator 
          p_it=(post_dom?node.out:node.in).begin();
          !changed && p_it!=(post_dom?node.out:node.in).end();
          ++p_it)
        if(!dominators[p_it->first].empty() && G::nodes[p_it->first].marked)
        {
          dominators[current]=dominators[p_it->first];
          dominators[current].insert(current);
          changed=true;
        }

    // compute intersection of predecessors
    for(typename G::edgest::const_iterator 
          p_it=(post_dom?node.out:node.in).begin();
        p_it!=(post_dom?node.out:node.in).end();
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
      for(typename G::edgest::const_iterator 
            s_it=(post_dom?node.in:node.out).begin();
          s_it!=(post_dom?node.in:node.out).end();
          ++s_it)
      {
        // check for marked G::nodes only
        if(G::nodes[s_it->first].marked && !G::nodes[s_it->first].deleted)
        {
          worklist.push_back(s_it->first);
        }
      }
    }
  }
}

