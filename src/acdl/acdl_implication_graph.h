/*******************************************************************\

Module: Implication graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_IMPLICATION_GRAPH_H
#define CPROVER_ACDL_IMPLICATION_GRAPH_H

#include "../ssa/local_ssa.h"
#include <util/graph.h>
#include "acdl_domain.h"
#include "graph_dominators.h"

class acdl_graph_dominatort;
class acdl_implication_graph_nodet : public graph_nodet<empty_edget>
{
public:
  bool is_decision;
  unsigned level;
  bool conflict;
  bool deleted;
  acdl_domaint::meet_irreduciblet expr;
  bool marked;
};

class acdl_implication_grapht : public graph<acdl_implication_graph_nodet>
{
public:  
  friend class acdl_graph_dominatort;
  explicit acdl_implication_grapht()
   : current_level(0)
  {}
  
  typedef std::vector<acdl_domaint::meet_irreduciblet> decision_trail;  
  decision_trail dec_trail; 
  
  unsigned current_level;
  void first_uip(nodest &cut);
  void add_deductions(const local_SSAt &SSA, const acdl_domaint::deductionst &m_ir);
  void add_deduction(const local_SSAt &SSA, const acdl_domaint::deductiont &m_ir);
  void add_decision(const acdl_domaint::meet_irreduciblet & m_ir);
  void print_graph_output(const local_SSAt &SSA);
  void output_graph(const local_SSAt &SSA, std::ostream &out) const;
  void output_graph_node(const local_SSAt &SSA, std::ostream &out, node_indext n) const; 

  void to_value(acdl_domaint::valuet &value) const;
  void remove_in_edges(node_indext n);
  void remove_out_edges(node_indext n);
  int graph_size();  
  acdl_implication_graph_nodet::node_indext find_node(const exprt &expr);
  void delete_graph_nodes(); 
  void mark_node(node_indext start);

protected:
};


#endif
