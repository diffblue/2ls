/*******************************************************************\

Module: Implication graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_CONFLICT_GRAPH_H
#define CPROVER_ACDL_CONFLICT_GRAPH_H

#include <goto-programs/property_checker.h>
#include "acdl_domain.h"
#include "../ssa/local_ssa.h"
#include <util/numbering.h>

class acdl_conflict_grapht
{
public:
   explicit acdl_conflict_grapht()
    : 
    current_level(0)
    {}
    
   ~acdl_conflict_grapht()
   {}

   int current_level;
   typedef std::vector<acdl_domaint::meet_irreduciblet> propagation_trail;
   propagation_trail prop_trail;
   typedef std::vector<acdl_domaint::meet_irreduciblet> decision_trail;
   // indexed by decision level
   typedef std::vector<std::vector<acdl_domaint::meet_irreduciblet> > declevel_prop_trail;
   typedef std::vector<unsigned> val_stackst;
   typedef std::vector<unsigned> control_stackt;
   typedef std::pair<int, int> intv;
   typedef std::vector<intv> valuest;
   valuest values;

   // scrap dec_trail in the future 
   decision_trail dec_trail;
   declevel_prop_trail dec_ded_trail;
   val_stackst val_trail;
   control_stackt control_trail;
  
   // indexed by numbering of meet_irreducible 
   typedef std::vector<std::vector<unsigned> > dlevelst;
   dlevelst dlevels;
   // numbering all meet_irreducibles
   typedef hash_numbering<exprt, irep_hash> meet_ird_numberingt;
   meet_ird_numberingt numbering;
   // numbering all variables 
   typedef hash_numbering<symbol_exprt, irep_hash> sym_numberingt;
   sym_numberingt numbering_symbol;
  
   void add_deductions(const local_SSAt &SSA, const acdl_domaint::deductionst &m_ir);
   void add_decision(const acdl_domaint::meet_irreduciblet &m_ir);
   void assign(acdl_domaint::meet_irreduciblet &exp);
   void to_value(acdl_domaint::valuet &value) const;
   void check_consistency();
   void init();
   void assign_to_trail(acdl_domaint::meet_irreduciblet &m_ir);
   void dump_trail(const local_SSAt &SSA);
 protected:
};
#endif

    
      

