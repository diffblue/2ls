/*******************************************************************\

Module: Conflict graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include "acdl_conflict_graph.h"
#define DEBUG

/*******************************************************************\

Function: acdl_conflict_grapht::add_deductions

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::add_deductions
  (const local_SSAt &SSA, const acdl_domaint::deductionst &m_ir)
{
  // iterate over the deductions
  for(std::vector<acdl_domaint::deductiont>::const_iterator it 
	= m_ir.begin(); it != m_ir.end(); it++)
  {
    std::cout << "conflict graph: " << from_expr(SSA.ns, "", it->first) << std::endl;
    // note that consequents are unique 
    acdl_domaint::meet_irreduciblet exp = it->first; 
    // number the meet_irreducible
    unsigned sym_no = numbering.number(exp); 
    // push it to prop_trail
    prop_trail.push_back(exp);
    val_trail.push_back(sym_no);
  }
}

/*******************************************************************\

Function: acdl_conflict_grapht::add_decision

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::add_decision
    (const acdl_domaint::meet_irreduciblet &m_ir)
{
  ++current_level;
  control_trail.push_back(prop_trail.size());
  acdl_domaint::meet_irreduciblet exp = m_ir; 
  prop_trail.push_back(exp);
  // number the meet_irreducible
  unsigned sym_no = numbering.number(exp); 
  val_trail.push_back(sym_no);
  dec_trail.push_back(exp);
  //dlevels[sym_no].push_back(current_level);
}

/*******************************************************************\

Function: acdl_conflict_grapht::to_value

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::to_value(acdl_domaint::valuet &value) const
{
  
  for(unsigned i=0;i<prop_trail.size();i++) {
    value.push_back(prop_trail[i]);
  }

  std::cout << "prop_trail size is: " << prop_trail.size() << std::endl;
  if(control_trail.size() != 0)
    std::cout << "control_trail.back is: " << control_trail.back() << std::endl;
  else  
    std::cout << "control_trail is empty" << std::endl;
#if 0  
  // this happens only for the first deduction phase
  if(control_trail.size() == 0) {
   for(unsigned i=0;i<prop_trail.size();i++) {
     // if there is a BOTTOM or false_exprt in the trail,
     // it should have been popped during backtracking
     //if(prop_trail[i] != false_exprt());
      value.push_back(prop_trail[i]);
   }
  }
  // this is normal case 
  else {
    unsigned trail_size = control_trail.back();
    for(unsigned i=0;i<trail_size;i++) {
      // if there is a BOTTOM or false_exprt in the trail,
      // it should have been popped during backtracking
      //if(prop_trail[i] != false_exprt());
       value.push_back(prop_trail[i]);
    }
  }
#endif  
}

/*******************************************************************\

Function: acdl_conflict_grapht::init

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::init()
{
  assert(prop_trail.size() == 0);
  assert(val_trail.size() == 0);
  assert(dec_trail.size() == 0);
  assert(control_trail.size() == 0);
}

/*******************************************************************\

Function: acdl_conflict_grapht::check_consistency

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_conflict_grapht::check_consistency()
{
  acdl_domaint::valuet val;
  for(unsigned i=0;i<prop_trail.size();i++) {
    // if there is a BOTTOM or false_exprt in the trail,
    // it should have been popped during backtracking
    assert(prop_trail[i] != false_exprt());
  }
}

/*******************************************************************\

Function: acdl_conflict_grapht::assign_to_trail

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::assign_to_trail
    (acdl_domaint::meet_irreduciblet &m_ir)
{
  prop_trail.push_back(m_ir);
  // number the meet_irreducible
  unsigned sym_no = numbering.number(m_ir); 
  val_trail.push_back(sym_no);
}

/*******************************************************************\

Function: acdl_conflict_grapht::print_output

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::dump_trail(const local_SSAt &SSA)
{
  std::cout << "Dump the trail" << std::endl;
  for(unsigned i=0;i<prop_trail.size();i++) { 
    std::cout << "Prop trail:" << from_expr(SSA.ns, "", prop_trail[i]) << std::endl;
    std::cout << "Val trail:" << from_expr(SSA.ns, "", numbering[val_trail[i]]) << std::endl;
  }
}
