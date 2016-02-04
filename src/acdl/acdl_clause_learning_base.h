/*******************************************************************\

Module: Implication graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_IMPLICATION_GRAPH_H
#define CPROVER_ACDL_IMPLICATION_GRAPH_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_clause_learning_baset : public messaget
{
public: 
   
 explicit acdl_clause_learning_baset()
 {
 }
 
  typedef struct {
    typedef std::list<acdl_domaint::meet_irreduciblet> asgn_antecedent; 
    // an important property of elements of partial assignments is that 
    // they must be complementable (needed for clause learning)
    std::map<acdl_domaint::meet_irreduciblet, asgn_antecedent> deductions_list;
    // edges pointing from a node (meet irrd) to another (meet irrd)
    std::map<acdl_domaint::meet_irreduciblet, acdl_domaint::meet_irreduciblet> edges;
    // clause database, which need to be added 
    // to SSA as conditionals
    typedef std::list<acdl_domaint::meet_irreduciblet> conflict_clauses;
    unsigned int level;
  } implication_grapht;
 /*virtual ~acdl_clause_learning_baset()
 {
 }*/

  virtual void add_deductions(const acdl_domaint::meet_irreduciblet &m_ir);
  virtual void add_decisions(const acdl_domaint::meet_irreduciblet & m_ir);
 virtual void backtrack_to_level(unsigned int index);

protected:
  implication_grapht g;
  
};

#endif
