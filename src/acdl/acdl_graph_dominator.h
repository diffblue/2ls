/**************************************************\

Module: ACDL acdl_implication_graphtraph Dominator 

Author: Rajdeep Mukherjee, Peter Schrammel

\**************************************************/

#ifndef CPROVER_ACDL_acdl_implication_graphtRAPH_DOMINATOR_H
#define CPROVER_ACDL_acdl_implication_graphtRAPH_DOMINATOR_H

#include "graph_dominators.h"
#include "acdl_implication_graph.h"

class acdl_graph_dominatort : 
 public graph_dominators_templatet<acdl_implication_grapht, false>
{
  public:
   virtual void initialise(acdl_implication_grapht &graph);
   virtual void fixedpoint(acdl_implication_grapht &graph);
    
  virtual void operator()(acdl_implication_grapht &graph, typename acdl_implication_grapht::node_indext entry_node);

  protected:
};

#endif
