/*******************************************************************\

Module: ACDL Decision Heuristics (Branch on Equality decisions)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_equality.h"

#define DEBUG 1

acdl_domaint::meet_irreduciblet acdl_decision_heuristics_equalityt::operator()  
    (const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
#ifdef DEBUG
  std::cout << "Printing the value inside decision" << std::endl;
  for(unsigned i=0;i<value.size();i++)
    std::cout << from_expr(value[i]) << ", " << std::endl;

  std::cout << "Printing all decision variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=decision_variables.begin(); it!=decision_variables.end(); it++)
    std::cout << from_expr(*it) << ", " << std::endl;
  
  std::cout << "Printing all read only variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=read_vars.begin(); it!=read_vars.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;
  
  std::cout << "Printing all assumption variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=assumption_vars.begin(); it!=assumption_vars.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;
  
  std::cout << "Printing all conditional variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=conditional_vars.begin(); it!=conditional_vars.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;
#endif

  // copy the value to non-constant value
  acdl_domaint::valuet v;
  for(unsigned k=0;k<value.size();k++)
    v.push_back(value[k]);

  // Priority of the decision variables selected (low value means high priority)
  // Priority 0: cond variables
  // Priority 1: non-cond assumption variables (only equality)
  // Priority 2: assumption variables [TBD: Change Phase]
  // Priority 3: read only variables
  // Priority 3: vars in assertions [TBD]
  // Priority 4: rest vars [TBD]

  // collect the non-singleton variables
  std::set<exprt> non_singletons;
  std::vector<exprt> singletons;
  acdl_domaint::meet_irreduciblet val;
  for(std::set<exprt>::const_iterator it=decision_variables.begin(); 
      it!=decision_variables.end(); ++it) {
#ifdef DEBUG
    std::cout << "Splitting for " << from_expr(*it) << std::endl;
#endif
    val=domain.split(value, *it);
    if(!val.is_false())
      non_singletons.insert(*it);
    // collect all singleton variables
    else
      singletons.push_back(*it);
  }

  // no more decisions can be made
  if(non_singletons.size()==0) {
#ifdef DEBUG
    std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
#endif
    return false_exprt();
  }

#ifdef DEBUG
  std::cout << "Printing all non-singletons decision variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=non_singletons.begin(); it!=non_singletons.end(); it++)
    std::cout << from_expr(*it) << ", " << std::endl;
#endif

 bool decision = false; 
 // ***************************************************************
 // make decision on cond variable followed by equality constraint on 
 // assumption variables followed by normal read_only variables
 // ***************************************************************
 std::set<exprt> conds_ns;
 std::set<exprt> non_conds_ns;
 // convert symbol_exprt to exprt
 
  
 set_intersection(conditional_vars.begin(), conditional_vars.end(), 
     non_singletons.begin(), non_singletons.end(), 
     std::inserter(conds_ns, conds_ns.begin()));
 set_intersection(assumption_vars.begin(), assumption_vars.end(),
     non_singletons.begin(), non_singletons.end(), 
     std::inserter(non_conds_ns, non_conds_ns.begin()));

  std::cout << "Printing non-singleton conditional variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=conds_ns.begin(); it!=conds_ns.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;
  
  std::cout << "Printing non-singleton assumption variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=non_conds_ns.begin(); it!=non_conds_ns.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;
 // Make decision on conditional variables
 // initialize the vectors with true
 std::vector<bool> conds_marked(conds_ns.size(), true);
 std::vector<bool> non_cond_marked(non_conds_ns.size(), true);
 
 if(conds_ns.size() > 0 || non_conds_ns.size() > 0) {
   assert(bad_decisions.size() == 0);
   // bad decisions can either be repeatative 
   // decisions or decision which are subsumed
   while(!decision && bad_decisions.size()<1) {
     bool cond_dec_left=false;
     bool non_cond_dec_left=false;
     // make decisions only if
     // there are non-singletons
     for(unsigned j=0;j<conds_ns.size();j++) {
       if(conds_marked[j]!=false) {
         cond_dec_left=true;
       }
     }
     for(unsigned k=0;k<non_conds_ns.size();k++) {
       if(non_cond_marked[k]!=false) {
         non_cond_dec_left=true;
       }
     }
     if(!cond_dec_left && !non_cond_dec_left) {
#ifdef DEBUG
       std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
#endif
       return false_exprt();
     }

     // assert there are some non-singletons
     assert(cond_dec_left || non_cond_dec_left);

     // check for cond variable
     bool cond=false;
     for(unsigned i=0;i<conds_ns.size();i++) {
       assert(conds_ns.size()>0);
       const acdl_domaint::meet_irreduciblet
         exp = *std::next(conds_ns.begin(), i);
       std::cout << "Checking cond variable " << from_expr(exp) << std::endl;
       val=domain.split(value, exp);
       if(!val.is_false()) {
         unsigned status=domain.compare_val_lit(v, val);
         if(status!=0) {
           // check that the decision is not 
           // subsumed by value. This also checks
           // for repeated decision from generating
           if(!domain.is_subsumed(val, value)) {
             decision=true;
             cond=true;
             decision_container.push_back(val);
             return val;
           }
           else { 
             decision=false;
             bad_decisions.push_back(val);
           }
         }
         else
           continue;
       }
       else {
         // mark the cond that is already singleton
         conds_marked[i]=false;
       }
     }
     // assert that the assumption cond set is exhausted
     assert(cond==false);

     // ***********************************
     // perform equality decisions (x==N) 
     // on non-cond assumption variables
     // ***********************************
     // [???] assert(conds_ns.size()==0);
     if(non_conds_ns.size() != 0) {
       acdl_domaint::valuet val_check=value;
       if(equality_decision_container.size() == 0) {
         // copy the value
         for(unsigned i=0;i<non_conds_ns.size();i++) {
           assert(non_conds_ns.size()>0);
           const acdl_domaint::meet_irreduciblet
             cexp = *std::next(non_conds_ns.begin(), i);
#ifdef DEBUG 
           std::cout << "Splitting for the variable " 
             << from_expr(cexp) << std::endl;
#endif
           //if(non_cond_marked[index]==false) continue;
           val=domain.split(value, cexp);
           if(!val.is_false()) {
             unsigned status=domain.compare_val_lit(v, val);
             if(status!=0) {
               //decision=true;
               // convert x<=10 to x==10
               assert(val.id()!=ID_not);
               const exprt &lhs=to_binary_relation_expr(val).lhs();
               const exprt &rhs=to_binary_relation_expr(val).rhs();
               std::cout << "lhs is " << from_expr(lhs) << std::endl;
               std::cout << "rhs is " << from_expr(rhs) << std::endl;
               exprt new_exp=equal_exprt(lhs, rhs);
               std::cout << "Equality decision: " << from_expr(new_exp) << std::endl;
               equality_decision_container.push_back(new_exp);
               std::cout << "Inserted into vector" << std::endl;
             }
             else {
#ifdef DEBUG
               std::cout << "cannot form equality decision" << std::endl;             
#endif
               continue;
             }
           }
           else {
             // mark the non_cond that is already singleton
             //non_cond_marked[index]=false;
             continue;
           }
         }
       }
       for(std::vector<exprt>::const_iterator
           ite=equality_decision_container.begin(); ite!=equality_decision_container.end(); ite++) 
         val_check.push_back(*ite);
       // check whether the set of decisions 
       // lead to a counterexample
       bool status = domain.gamma_complete_deduction(ssa_conjuncted, val_check);

       unsigned size = equality_decision_container.size();
       // return elements of equality_decision_container
       // since these decisions leads to counterexample
       if(status == 1 && size > 0) {
         /*[CHECK] Does the equality decisions handled 
          * properly by the underlying domain or it blocks
          * some obvious deductions due to expressivility*/

         /*[IMPORTANT] Do not record the decisions and deductions 
          * from the equality decisions in the trail if it does 
          * not lead to counterexample. */

#ifdef DEBUG
         std::cout << "Printing all equality decisions that leads to counterexample" << std::endl;
         for(std::vector<exprt>::const_iterator
             ite=equality_decision_container.begin(); ite!=equality_decision_container.end(); ite++) 
           std::cout << from_expr(*ite) << ", " << std::endl;
         std::cout << "Size: "  << size << std::endl;
#endif
         decision = true;

         exprt dec_val = equality_decision_container.back();
         equality_decision_container.pop_back();
         //equality_decision_container.erase(itb);
#ifdef DEBUG
         std::cout << "Printing all equality decisions after deleting one item" << std::endl;
         for(std::vector<exprt>::const_iterator
             ite=equality_decision_container.begin(); ite!=equality_decision_container.end(); ite++) 
           std::cout << from_expr(*ite) << ", " << std::endl;
         std::cout << "Size after deletion: "  << equality_decision_container.size() << std::endl;
#endif
         assert(size == (equality_decision_container.size()+1));

         if(!domain.is_subsumed(dec_val, value)) {
           decision=true;
           cond=true;
           decision_container.push_back(dec_val);
           return dec_val;
         }
         else { 
           decision=false;
           bad_decisions.push_back(val);
         }
       }

       // **************************************
       // perform less aggressive decisions 
       // on the non-cond assumption variables
       // **************************************
       //if(equality_decision_container.size() == 0) 
       else 
       {
         // make decisions on non-cond variables
         unsigned index=rand() % non_conds_ns.size();
         /*const acdl_domaint::meet_irreduciblet cexp=
           non_conds_ns[index];*/
         assert(non_conds_ns.size()>0);
         const acdl_domaint::meet_irreduciblet
           cexp = *std::next(non_conds_ns.begin(), index);
         // this variable is already singleton
         if(non_cond_marked[index]==false) continue;
         val=domain.split(value, cexp);
         if(!val.is_false()) {
           unsigned status=domain.compare_val_lit(v, val);
           if(status!=0) {
             if(!domain.is_subsumed(val, value)) {
               decision=true;
               cond=true;
               decision_container.push_back(val);
               return val;
             }
             else { 
               decision=false;
               bad_decisions.push_back(val);
             }
           }
           else
             continue;
         }
         else {
           // mark the non_cond that is already singleton
           non_cond_marked[index]=false;
           continue;
         }
       }
     }  // end of non-cond assumption variables
   } // end of while loop for assumption variables and cond variables
 }

#ifdef DEBUG 
 std::cout << "There are no remaining conditional and assumption variables" << std::endl; 
#endif

 assert(decision != true);
 // clear the assumption variables
 assumption_vars.clear();
 
 // ************************************
 // make decision on read-only variables
 // *************************************
 
 std::set<exprt> read_only_ns;
 set_intersection(non_singletons.begin(), non_singletons.end(),
     read_vars.begin(), read_vars.end(), 
     std::inserter(read_only_ns, read_only_ns.begin()));
  
 if(read_only_ns.size()) {
   // initialize the vectors with true
   std::vector<bool> read_only_ns_mark(read_only_ns.size(), true);
   while(!decision) {
     bool non_cond_dec_left=false;
     // make decisions only if
     // there are non-singletons
     for(unsigned k=0;k<read_only_ns.size();k++) {
       if(read_only_ns_mark[k]!=false) {
         non_cond_dec_left=true;
       }
     }
     if(!non_cond_dec_left) {
#ifdef DEBUG
       std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
#endif
       return false_exprt();
     }

     // assert there are some non-singletons
     assert(non_cond_dec_left);

     // make decisions on non-cond variables
     unsigned index=rand() % read_only_ns.size();
     assert(read_only_ns.size()>0);
     const acdl_domaint::meet_irreduciblet
       cexp = *std::next(read_only_ns.begin(), index);
     // this variable is already singleton
     if(read_only_ns_mark[index]==false) continue;
     val=domain.split(value, cexp);
     std::cout << "Decisions on read only variable " << from_expr(cexp) << std::endl;
     if(!val.is_false()) {
       unsigned status=domain.compare_val_lit(v, val);
       if(status!=0) {
         if(!domain.is_subsumed(val, value)) {
           decision=true;
           decision_container.push_back(val);
           return val;
         }
         else { 
           decision=false;
           bad_decisions.push_back(val);
         }
       }
       else
         continue;
     }
     else {
       // mark the non_cond that is already singleton
       read_only_ns_mark[index]=false;
       continue;
     }
   }  // end of while
 }
 assert(decision != true);


 // ************************************
 // make decision on rest variables
 // *************************************
 
 // non-singletons - conditional_vars
 non_singletons.erase(conditional_vars.begin(), conditional_vars.end());
 // non-singletons - assumption_vars
 non_singletons.erase(assumption_vars.begin(), assumption_vars.end());
 // non-singletons - read_vars
 non_singletons.erase(read_vars.begin(), read_vars.end());
 
 // now clear the read_only variables
 read_vars.clear();
 // now clear the conditional variables
 conditional_vars.clear();
 
 std::set<exprt> rest_ns;
 rest_ns.insert(non_singletons.begin(), non_singletons.end());
 if(rest_ns.size()) 
 {
   // initialize the vectors with true
   std::vector<bool> rest_ns_mark(rest_ns.size(), true);
   while(!decision) {
     bool non_cond_dec_left=false;
     // make decisions only if
     // there are non-singletons
     for(unsigned k=0; k<rest_ns.size(); k++) {
       if(rest_ns_mark[k]!=false) {
         non_cond_dec_left=true;
       }
     }
     if(!non_cond_dec_left) {
#ifdef DEBUG
       std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
#endif
       return false_exprt();
     }

     // assert there are some non-singletons
     assert(non_cond_dec_left);

     // make decisions on non-cond variables
     unsigned index=rand() % rest_ns.size();
     assert(!rest_ns.empty());
     const acdl_domaint::meet_irreduciblet
       cexp = *std::next(rest_ns.begin(), index);
     // this variable is already singleton
     if(rest_ns_mark[index]==false) continue;
     val=domain.split(value, cexp);
     std::cout << "Decisions on rest variable " << from_expr(cexp) << std::endl;
     if(!val.is_false()) {
       unsigned status=domain.compare_val_lit(v, val);
       if(status!=0) {
         if(!domain.is_subsumed(val, value)) {
           decision=true;
           decision_container.push_back(val);
           return val;
         }
         else { 
           decision=false;
           bad_decisions.push_back(val);
         }
       }
       else
         continue;
     }
     else {
       // mark the non_cond that is already singleton
       rest_ns_mark[index]=false;
       continue;
     }
   }  // end of while
 }

 if(bad_decisions.size()>1) 
   std::cout << "The decision can not infer new element, change the phase !!"  << std::endl;

 // if the control reaches here, 
 // then return false_exprt
 return false_exprt();
}
