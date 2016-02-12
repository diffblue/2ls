/*******************************************************************\

Module: Implication graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_IMPLICATION_GRAPH_H
#define CPROVER_ACDL_IMPLICATION_GRAPH_H

#include <util/graph.h>
#include "acdl_domain.h"

class acdl_implication_graph_nodet : public graph_nodet<empty_edget>
{
public:
  bool is_decision;
  unsigned level;
  acdl_domaint::meet_irreduciblet expr;
};

class acdl_implication_grapht : public graph<acdl_implication_graph_nodet>
{
public:
  explicit acdl_implication_grapht()
    :
    current_level(0)
  {}
  
  void first_uip() { assert(false); }
  void add_deductions(const acdl_domaint::deductionst &m_ir);
  void add_deduction(const acdl_domaint::deductiont &m_ir);
  void add_decision(const acdl_domaint::meet_irreduciblet & m_ir);

  void to_value(acdl_domaint::valuet &value);
  
protected:
  unsigned current_level;
};

#endif
