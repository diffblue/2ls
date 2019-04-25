/*******************************************************************\

Module: Abstract domain base class

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Abstract domain base class

#ifndef CPROVER_2LS_DOMAINS_DOMAIN_H
#define CPROVER_2LS_DOMAINS_DOMAIN_H

#include <iostream>
#include <set>

#include <util/std_expr.h>
#include <util/i2string.h>
#include <langapi/language_util.h>
#include <util/replace_expr.h>
#include <util/namespace.h>
#include <solvers/refinement/bv_refinement.h>

// Forward declaration - real is in template_generator_base.h
class template_generator_baset;
class local_SSAt;

class domaint
{
public:
  domaint(
    unsigned _domain_number,
    replace_mapt &_renaming_map,
    const namespacet &_ns):
    domain_number(_domain_number),
    renaming_map(_renaming_map),
    ns(_ns)
  {
  }

  virtual ~domaint()
  {
  }

  typedef exprt vart;
  typedef std::vector<vart> var_listt;
  typedef std::set<vart> var_sett;

  typedef enum {LOOP, IN, OUT, OUTL, OUTHEAP} kindt;

  typedef exprt guardt;
  typedef unsigned rowt;

  typedef struct
  {
    guardt pre_guard;
    guardt post_guard;
    vart var;
    exprt aux_expr; // some auxiliary per-variable constraint
    kindt kind;
  } var_spect;

  typedef std::vector<var_spect> var_specst;

  // handles on values to retrieve from model
  bvt strategy_cond_literals;
  exprt::operandst strategy_value_exprs;


  class valuet
  {
  public:
    typedef enum {TOP, BOTTOM, OTHER} basic_valuet;
    valuet():basic_value(OTHER) {}
    virtual ~valuet()  {}

    basic_valuet basic_value;
  };

  virtual void initialize(valuet &value) { value.basic_value=valuet::BOTTOM; }

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Initialize SMT solver when new strategy solver is created.
             Returned value is written into SMT solver.

  \*******************************************************************/
  virtual const exprt initialize_solver(
    const local_SSAt &SSA,
    const exprt &precondition,
    template_generator_baset &template_generator);

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Initialize strategy solver at beginning of each iteration.

  \*******************************************************************/
  virtual void solver_iter_init(valuet &value);

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Domain should return true if wants to improve its invariants.
             Otherwise no further improvements of invariants is done.

  \*******************************************************************/
  virtual bool has_something_to_solve();

  /*******************************************************************\

    Function: domaint::get_current_loop_guard

    Inputs:

    Outputs:

    Purpose: Return current loop guard.

  \*******************************************************************/

  virtual exprt get_current_loop_guard(size_t row);

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Edit invariant based on current model of satisfiability

  \*******************************************************************/

  virtual bool edit_row(const rowt &row, valuet &inv, bool improved)=0;

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: After each iteration of strategy solver it is possible to write
             expression into SMT solver, which stay present in further
             iterations.

  \*******************************************************************/
  virtual exprt make_permanent(valuet &value);

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Finalize domain - last step of each iteration of strategy solver.

  \*******************************************************************/
  virtual void post_edit();

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Create entry constraints as a conjuction of entry expressions
             for each template row.

  \*******************************************************************/
  /*
   */
  virtual exprt to_pre_constraints(valuet &value)=0;

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Create exit constraints for each value row. Each expression is
             a negation of a row expression
             (for solving the "exists forall" problem)

  \*******************************************************************/
  virtual void make_not_post_constraints(
    valuet &value,
    exprt::operandst &cond_exprs)=0;

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Required values from SMT solver

  \*******************************************************************/
  virtual std::vector<exprt> get_required_smt_values(size_t row)=0;

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Domain can save vales from SMT solver (required by
             get_required_smt_values) into internal representation

  \*******************************************************************/
  virtual void set_smt_values(std::vector<exprt> got_values, size_t row)=0;

  /*******************************************************************\

    Function: domaint::

    Inputs:

    Outputs:

    Purpose: Method called when model is unsatisfiable

  \*******************************************************************/
  virtual bool handle_unsat(valuet &value, bool improved);

  // returns true as long as further refinements are possible
  virtual void reset_refinements() { }
  virtual bool refine() { return false; }

  virtual void join(valuet &value1, const valuet &value2)
  {
    bool other_bottom=
      value1.basic_value==valuet::OTHER &&
      value2.basic_value==valuet::BOTTOM;
    if(value1.basic_value==value2.basic_value ||
       value1.basic_value==valuet::TOP ||
       other_bottom)
      return;
    value1.basic_value=value2.basic_value;
  }

  virtual void output_value(
    std::ostream &out,
    const valuet &value,
    const namespacet &ns) const
  {
    assert(false);
  }

  virtual void output_domain(
    std::ostream &out,
    const namespacet &ns) const
  {
    assert(false);
  }

  // (not useful to make value const (e.g. union-find))
  virtual void project_on_vars(
    valuet &value,
    const var_sett &vars,
    exprt &result)
  {
    if(value.basic_value==valuet::BOTTOM)
      result=false_exprt();
    else
      result=true_exprt();
  }

  static kindt merge_kinds(kindt k1, kindt k2);

  static void output_var_specs(
    std::ostream &out,
    const var_specst &var_specs,
    const namespacet &ns);

protected:
  unsigned domain_number; // serves as id for variables names
  replace_mapt &renaming_map;
  const namespacet &ns;

  inline void rename(exprt &expr)
  {
    replace_expr(renaming_map, expr);
  }

  inline void rename(exprt::operandst &operands)
  {
    for(unsigned i=0; i<operands.size(); ++i)
      replace_expr(renaming_map, operands[i]);
  }
};

#endif // CPROVER_2LS_DOMAINS_DOMAIN_H
