/*******************************************************************\

Module: ACDL Worklist Management Interface

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_2LS_ACDL_ACDL_WORKLIST_BASE_H
#define CPROVER_2LS_ACDL_ACDL_WORKLIST_BASE_H

#include <goto-programs/property_checker.h>

#include "acdl_domain.h"
#include "../ssa/local_ssa.h"

class acdl_worklist_baset : public messaget
{
public:
  typedef std::list<acdl_domaint::statementt> worklistt;
  typedef std::map<acdl_domaint::statementt, acdl_domaint::varst> stmt_var_pairt;
  // typedef std::list<std::pair<acdl_domaint::statementt, acdl_domaint::varst>> worklistt;

  explicit acdl_worklist_baset()
  {
  }

  virtual ~acdl_worklist_baset()
  {
  }

  // this is temporary container which is used
  // to update the live varaible list for each
  // statement. When the update is complete, this
  // list must be flushed.
  acdl_domaint::varst live_var_list;
  typedef std::list<acdl_domaint::statementt> assert_listt;
  assert_listt alist;


  virtual void initialize(const local_SSAt &, const exprt &, const exprt&)
  { assert(false); }

  // [TODO] Will go away-temporary for forward strategy
  /*virtual void initialize_forward(const local_SSAt &, const exprt &, const exprt&)
    { assert(false); }
  */

  virtual void dec_update(const local_SSAt &SSA, const acdl_domaint::meet_irreduciblet &stmt,
                          const exprt& assertion) { assert(false); }

  void slicing (const local_SSAt &SSA,
                const exprt &assertion, const exprt& additional_constraint);

  void initialize_live_variables();
  //  { assert(false); }
  virtual void select_vars(const exprt &statement, acdl_domaint::varst &vars);

  virtual void update(const local_SSAt &SSA,
                      const acdl_domaint::varst &new_vars,
                      const acdl_domaint::statementt &statement=nil_exprt(), const exprt& assertion=true_exprt())
  { assert(false); }


  const acdl_domaint::statementt pop ();

  void push_into_assertion_list (assert_listt &aexpr,
                                 const acdl_domaint::statementt &statement);

  inline bool empty() const { return worklist.empty(); }

  acdl_domaint::varst check_var_liveness (acdl_domaint::varst &vars);
  acdl_domaint::varst live_variables;
  acdl_domaint::varst worklist_vars;
  acdl_domaint::varst leaf_vars;

  typedef std::vector<exprt> statement_listt;
  statement_listt statements;
  typedef std::list<acdl_domaint::statementt> listt;

  void update (const local_SSAt &SSA,
               const acdl_domaint::varst &vars,
               listt &lexpr,
               const acdl_domaint::statementt &current_statement,
               const exprt& assertion);

  void push (const acdl_domaint::statementt &statement);
  void push_into_map (const acdl_domaint::statementt &statement, const acdl_domaint::varst &lvars);
  virtual acdl_domaint::varst pop_from_map (const acdl_domaint::statementt &statement) { assert(false); }
  void delete_from_map (const acdl_domaint::statementt &statement);
  void delete_map();
  void print_worklist();
  void push_into_list (listt &lexpr,
                       const acdl_domaint::statementt &statement);

  const acdl_domaint::statementt pop_from_list (listt &lexpr);

protected:
  worklistt worklist;
  stmt_var_pairt svpair;

  void remove_live_variables (const local_SSAt &SSA,
                              const acdl_domaint::statementt & statement);
  bool check_statement (const exprt &expr, const acdl_domaint::varst &vars);

};

#endif
