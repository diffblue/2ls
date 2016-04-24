/*******************************************************************\

Module: ACDL Worklist Management Interface

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_WORKLIST_BASE_H
#define CPROVER_ACDL_WORKLIST_BASE_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_worklist_baset : public messaget
{
public:
  typedef std::list<acdl_domaint::statementt> worklistt;
  typedef std::list<acdl_domaint::statementt> assert_listt;
  assert_listt alist;
  virtual void initialize(const local_SSAt &)
    { assert(false); }

  virtual void dec_update(const local_SSAt &SSA, const acdl_domaint::statementt &stmt) { assert(false); }

  
  virtual void initialize_live_variables()
  { assert(false); }
  virtual void select_vars(const exprt &statement, acdl_domaint::varst &vars);
  virtual void update(const local_SSAt &SSA,
		      const acdl_domaint::varst &new_vars,
		      const acdl_domaint::statementt &statement=nil_exprt());
    //{ assert(false); }

  const acdl_domaint::statementt pop ();

  void push_into_assertion_list (assert_listt &aexpr,
				 const acdl_domaint::statementt &statement);
  
  inline bool empty() const { return worklist.empty(); }
  
  acdl_domaint::varst check_var_liveness (acdl_domaint::varst &vars);
  acdl_domaint::varst live_variables;
  acdl_domaint::varst worklist_vars;
protected:
  worklistt worklist;
  
  explicit acdl_worklist_baset()
  {
  }  

  virtual ~acdl_worklist_baset() 
  {
  }

  void remove_live_variables (const local_SSAt &SSA, 
         const acdl_domaint::statementt & statement);
  bool check_statement (const exprt &expr, const acdl_domaint::varst &vars);
  void push (const acdl_domaint::statementt &statement);

};

#endif
