/*******************************************************************\

Module: Conflict graph implementation

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#include "acdl_conflict_graph.h"
//#define DEBUG

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
  for(std::vector<acdl_domaint::meet_irreduciblet>::const_iterator it 
	= m_ir.begin(); it != m_ir.end(); it++)
  {
#ifdef DEBUG    
    std::cout << "conflict graph: " << from_expr(SSA.ns, "", *it) << std::endl;
#endif    
    // note that consequents are unique 
    acdl_domaint::meet_irreduciblet exp = *it; 
    assign(exp);
  }
  // [TODO] Make it a map of <stmt, prop_trail_index>
  // reason_trail
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
  dec_trail.push_back(exp);
  assign(exp);
  //dlevels[sym_no].push_back(current_level);
}


/*******************************************************************\

Function: acdl_conflict_grapht::assign

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::assign
    (acdl_domaint::meet_irreduciblet &exp)
{
    // number the meet_irreducible
    unsigned sym_no = numbering.number(exp); 
    // push it to prop_trail
    prop_trail.push_back(exp);
    val_trail.push_back(sym_no);
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
#ifdef DEBUG
  std::cout << "prop_trail size is: " << prop_trail.size() << std::endl;
  if(control_trail.size() != 0)
    std::cout << "control_trail.back is: " << control_trail.back() << std::endl;
  else  
    std::cout << "control_trail is empty" << std::endl;
#endif
        
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
#ifdef DEBUG  
  std::cout << "Checking consistency of conflict graph" << std::endl;
#endif  
  acdl_domaint::valuet val;
  for(unsigned i=0;i<prop_trail.size();i++) {
    // if there is a BOTTOM or false_exprt in the trail,
    // it should have been popped during backtracking
    assert(prop_trail[i] != false_exprt());
  }
#ifdef DEBUG  
  std::cout << "Conflict graph is consistent" << std::endl;
#endif  
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
#ifdef DEBUG 
  std::cout << "Dump the trail" << std::endl;
  std::cout << "****************" << std::endl;
  std::cout << "Decision Level: " << current_level << std::endl;
#endif  
  int control_point;
  if(control_trail.size() == 0)
   control_point=0;
  else
   control_point=control_trail.back();
   
  // check if propagation trail is zero
  if(prop_trail.size() == 0) {
    std::cout << "The propagation trail is empty" << std::endl;
    return;
  }
   
  std::cout << "Upper index: " << prop_trail.size()-1 << "lower index: " << control_point << std::endl;
  for(unsigned i=prop_trail.size()-1;i>=control_point;i--) {
   std::cout << from_expr(SSA.ns, "", prop_trail[i]) << std::endl;
   if(i==0) break;
  }
   
  int search_level = control_trail.size()-1;
  while(search_level >= 0) {
    int upper_index=0;
    int lower_index=0;
    std::cout << "Decision Level: " << search_level << std::endl;
    upper_index = control_trail[search_level];
    if(search_level-1 >= 0)
      lower_index = control_trail[search_level-1];
    else 
      lower_index = 0; 

    std::cout << "Upper index: " << upper_index << "lower index: " << lower_index << std::endl;
    // Done for empty propagation trail 
    // at a particular search level
    if(upper_index==0) return;
    // now traverse the prop_trail  
    for(unsigned k=upper_index-1;k>=lower_index;k--) {
     std::cout << from_expr(SSA.ns, "", prop_trail[k]) << std::endl;
     if(k==0) break;
    }
    search_level=search_level-1;
  }
}

/*******************************************************************\

Function: acdl_conflict_grapht::print_output

  Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void acdl_conflict_grapht::dump_dec_trail(const local_SSAt &SSA)
{
  std::cout << "Dump the decision trail" << std::endl;
  for(unsigned i=0;i<dec_trail.size();i++) { 
    std::cout << "decision trail element:" << from_expr(SSA.ns, "", dec_trail[i]) << std::endl;
    //std::cout << "Val trail:" << from_expr(SSA.ns, "", numbering[val_trail[i]]) << std::endl;
  }
}
