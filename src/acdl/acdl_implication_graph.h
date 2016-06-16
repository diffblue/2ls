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
  // "level" is made signed just to compare with 
  // a negative value during backtracking
  //int level;
  bool conflict;
  bool deleted;
  acdl_domaint::meet_irreduciblet expr;
  bool marked;
  std::vector<int> dec_level;
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
  
  int current_level;
  acdl_implication_grapht::node_indext first_uip(const local_SSAt &SSA);
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
  exprt find_node_expr(node_indext n);
  int decision_level(node_indext n);
  acdl_implication_graph_nodet::node_indext find_node(const exprt &expr);
  void delete_graph_nodes(); 
  void mark_node(node_indext start);
  void unmark_nodes();
  acdl_implication_grapht::node_indext find_dec_node(node_indext n); 
  void get_reason (node_indext uip, acdl_domaint::valuet &reason);
  void check_consistency(int idx);
  void delete_in_nodes(node_indext n); 
  void delete_out_nodes(node_indext n); 

protected:
};


#endif
