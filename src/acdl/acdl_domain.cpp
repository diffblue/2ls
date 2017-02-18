/*******************************************************************\

Module: ACDL Domain

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/


#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <utility>
#include <algorithm>

#include <util/simplify_expr.h>
#include <util/find_symbols.h>
#include <memory>

#include "../domains/ssa_analyzer.h"
#include "../domains/tpolyhedra_domain.h"

#include "acdl_worklist_base.h"
#include "acdl_domain.h"
#include "template_generator_acdl.h"

#define NO_PROJECTION

/*******************************************************************\

Function: acdl_domaint::operator()

  Inputs:

 Outputs:

 Purpose: operator()

\*******************************************************************/

void acdl_domaint::operator()(
  const statementt &statement,
  const varst &vars,
  const valuet &old_value,
  valuet &new_value,
  deductionst &deductions)
{
#ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] old value: ";
  output(std::cout, old_value) << std::endl;
#endif

#ifdef DEBUG
  std::cout << "DOMAIN projected live variables are: ";
  for(acdl_domaint::varst::const_iterator
        it=vars.begin();it!=vars.end(); ++it)
    std::cout << from_expr(SSA.ns, "", *it) << " ";
  std::cout << std::endl;
#endif

  // partition variables
  varst bool_vars, num_vars;
  for(varst::const_iterator it=vars.begin();
      it!=vars.end(); ++it)
  {
    if(it->type().id()==ID_bool)
    {
      bool_vars.insert(*it);
    }
    else if (it->type().id()==ID_signedbv ||
             it->type().id()==ID_unsignedbv ||
             it->type().id()==ID_floatbv)
    {
      num_vars.insert(*it);
    }
    else
    {
      std::cout << "WARNING: do not know how to propagate "
                << it->get_identifier()
                << " of type " << from_type(SSA.ns, "", it->type())
                << std::endl;
    }
  }
  deductionst num_deductions;
  valuet num_new_value;
  // infer
  maps_to_bottom(statement, bool_vars, old_value,
                 new_value, deductions);
  if(deductions.empty())
  {
    bool_inference(statement, bool_vars, old_value,
                   new_value, deductions);
    numerical_inference(statement, num_vars, old_value,
                        num_new_value, num_deductions);
    // collect results
    new_value.insert(new_value.end(), num_new_value.begin(),
                     num_new_value.end());
    deductions.insert(deductions.end(), num_deductions.begin(),
                      num_deductions.end());
  }
#ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] deductions: ";
  output(std::cout, deductions) << std::endl;
#endif
}


/*******************************************************************\

Function: acdl_domaint::operator()

 Inputs:

 Outputs:

 Purpose: [TODO] operator() used for underapproximation

\*******************************************************************/
void acdl_domaint::operator()(
  const statementt &statement,
  const valuet &initial_value,
  valuet &final_value,
  valuet &new_value)
{

  // assert that new_value subsumes final_value
  // assert(0);
}



/*******************************************************************\

Function: acdl_domaint::maps_to_bottom()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::maps_to_bottom(
  const statementt &statement,
  const varst &vars,
  const valuet &old_value,
  valuet &new_value,
  deductionst &deductions)
{
#ifdef DEBUG
  std::cout << "checking whether statement maps to BOTTOM: ";
#endif
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));

  // get handles on meet irreducibles to check them later
  bvt value_literals;
  std::vector<int> value_literal_map;
  value_literals.reserve(old_value.size());
  *solver << statement;
  for(unsigned i=0; i<old_value.size(); i++)
  {
    literalt l=solver->convert(old_value[i]);
    if(l.is_constant())
    {
      *solver << literal_exprt(l);
      continue;
    }
    value_literal_map.push_back(i);
    value_literals.push_back(l);
    solver->solver->set_frozen(l);
  }
  solver->set_assumptions(value_literals);

  if((*solver)()==decision_proceduret::D_UNSATISFIABLE)
  {
#ifdef DEBUG
    std::cout << "yes, deducing BOTTOM" << std::endl;
#endif
    new_value.push_back(false_exprt());
    deductions.push_back(false_exprt());
  }
  else {
#ifdef DEBUG
    std::cout << "no" << std::endl;
#endif
  }
}

/*******************************************************************\

Function: acdl_domaint::bool_inference()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::bool_inference(
  const statementt &statement,
  const varst &vars,
  const valuet &_old_value,
  valuet &new_value,
  deductionst &deductions)
{
  deductions.reserve(vars.size());
  for(varst::const_iterator it=vars.begin();
      it!=vars.end(); ++it)
  {
    ssa_analyzert ssa_analyzer;
    std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));
    varst pvars;
    pvars.insert(*it);

    // project _old_value on everything in statement but *it
    valuet old_value;
    remove_vars(_old_value, pvars, old_value);

#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] projected(" << it->get_identifier() << "): ";
    output(std::cout, old_value) << std::endl;
#endif

    meet_irreduciblet deduced;

    // inference for booleans
    valuet var_value;
    literalt l=solver->solver->convert(*it);
    if(l.is_constant())
    {
      *solver << literal_exprt(l); // TODO: this has only an effect if l is false and then we have deduced a conflict
      continue; // in this case we don't have information on deductions
    }
    solver->solver->set_frozen(l);

    *solver << statement;
    *solver << conjunction(old_value);

    if((*solver)()==decision_proceduret::D_SATISFIABLE)
    {
      exprt m=solver->get(*it);
      if(m.is_true())
        deduced=*it;
      else
        deduced=not_exprt(*it);

      // test the complement
      solver->new_context();
      *solver << not_exprt(deduced);
#ifdef DEBUG
      std::cout << "deducing in SAT" << std::endl;
#endif
      if((*solver)()==decision_proceduret::D_SATISFIABLE)
      {
#ifdef DEBUG
        std::cout << "not deducing" << std::endl;
#endif
        // "don't know"
        // pop_context not needed
        continue;
      }
      else
      {
#ifdef DEBUG
        std::cout << "actually deducing" << std::endl;
#endif
        if(!is_subsumed_syntactic(deduced, _old_value))
        {
          new_value.push_back(deduced);
          deductions.push_back(deduced);
        }
      }

      // pop_context not needed
    }
    else // bottom
    {
#ifdef DEBUG
      std::cout << "deducing in BOTTOM" << std::endl;
#endif
      deductions.push_back(false_exprt());
      break; // at this point we have a conflict, we return
    }

#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] boolean deductions(" << it->get_identifier() << "): ";
    output(std::cout, deductions) << std::endl;
#endif
  }
}

/*******************************************************************\

Function: acdl_domaint::numerical_inference()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::numerical_inference(
  const statementt &statement,
  const varst &vars,
  const valuet &_old_value,
  valuet &new_value,
  deductionst &deductions)
{
  // add variables in old value
  varst tvars=vars;
  for(valuet::const_iterator it=_old_value.begin();
      it!=_old_value.end(); ++it)
  {
    varst symbols;
    find_symbols(*it, symbols);
    tvars.insert(symbols.begin(), symbols.end());
  }

#ifdef DEBUG
  std::cout << "The total number of variables passed to the template generator is " << tvars.size() << std::endl;
  std::cout << "The variables are " << std::endl;
  for(varst::const_iterator it=tvars.begin();
      it!=tvars.end(); ++it)
    std::cout << from_expr(*it) << ", " << std::endl;
#endif

  template_generator_acdlt template_generator(options, ssa_db, ssa_local_unwinder);
  template_generator.set_message_handler(get_message_handler());
  template_generator(SSA, tvars);

#ifdef NO_PROJECTION
  deductions.reserve(1);
#else
  deductions.reserve(vars.size());
  for(varst::const_iterator it=vars.begin();
      it!=vars.end(); ++it)
#endif
  {
    ssa_analyzert ssa_analyzer;
    std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));

    // project _old_value on everything in statement but *it
    valuet old_value;
#ifdef NO_PROJECTION
    old_value=_old_value;
#else
    remove_var(_old_value, *it, old_value);
#if def DEBUG
    std::cout << "[ACDL-DOMAIN] projected("
              << from_expr(SSA.ns, "", *it) << "): ";
    output(std::cout, old_value) << std::endl;
#endif
#endif

    meet_irreduciblet deduced;
    ssa_analyzer(*solver, SSA, and_exprt(conjunction(old_value), statement),
                 template_generator);
    exprt var_value;
    ssa_analyzer.get_result(var_value, template_generator.all_vars());
#if 0
    std::cout << "RESULT: " << from_expr(SSA.ns, "", var_value) << std::endl;
#endif
    valuet var_values;
    expr_to_value(simplify_expr(var_value, SSA.ns), var_values);

#ifdef DEBUG
    std::cout << "RESULT: "; output(std::cout, var_values) << std::endl;
#endif
    if(var_values.empty())
#ifdef NO_PROJECTION
      return;
#else
    continue;
#endif

    // get deductions
    // ENHANCE: make assumptions persistent in incremental_solver
    // so that we can reuse value+statement from above
    *solver << statement;
    *solver << conjunction(old_value);

    for(unsigned i=0; i<var_values.size(); ++i)
    {
      solver->new_context();
      *solver << not_exprt(var_values[i]);

      decision_proceduret::resultt result=(*solver)();
      assert(result==decision_proceduret::D_UNSATISFIABLE);

#ifdef DEBUG
      std::cout << "IS_SUBSUMED: " << std::endl;
      std::cout << "  " << from_expr(SSA.ns, "", var_values[i]) << std::endl;
      std::cout << "  "; output(std::cout, _old_value); std::cout << std::endl;
#endif
      if(!is_subsumed_syntactic(var_values[i], _old_value))
      {
#ifdef DEBUG
        std::cout << "adding new value " << from_expr(SSA.ns, "", var_values[i]) << std::endl;
#endif
        new_value.push_back(var_values[i]);
        deductions.push_back(var_values[i]);
      }
      solver->pop_context();
    }

#ifdef DEBUG
#ifdef NO_PROJECTION
    std::cout << "[ACDL-DOMAIN] numerical deductions: ";
    output(std::cout, deductions) << std::endl;
#else
    std::cout << "[ACDL-DOMAIN] numerical deductions("
              << from_expr(SSA.ns, "", *it) << "): ";
    output(std::cout, deductions) << std::endl;
#endif
#endif
  }
}

/*******************************************************************\

Function: acdl_domaint::meet()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::meet(const valuet &old_value,
                        valuet &new_value)
{
  new_value.insert(new_value.end(), old_value.begin(), old_value.end());
}

/*******************************************************************\

Function: acdl_domaint::meet()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::meet(const meet_irreduciblet &old_value,
                        valuet &new_value)
{
  new_value.push_back(old_value);
}

/*******************************************************************\

Function: acdl_domaint::join()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::join(const std::vector<valuet> &old_values,
                        valuet &new_value)
{
  assert(false);
}

/*******************************************************************\

Function: acdl_domaint::normalize_meetirrd()

  Inputs:  example: 1. !x<=3
                    2. !(x+y<=5)
  Outputs: example  1: x>3
                    2. (x+y>5)
\*******************************************************************/
void acdl_domaint::normalize_meetirrd(const meet_irreduciblet &m, meet_irreduciblet &mout) const 
{
    if(m.id()==ID_not) {
#ifdef DEBUG
      std::cout << "The original not expression is " << from_expr(m) << std::endl;
#endif
      const exprt &expb=m.op0();

      // Handle the singleton case: example : !guard#0
      if(expb.id()!=ID_le && expb.id()!=ID_ge)
      { }
      
      else 
      {
        const exprt &lhs=to_binary_relation_expr(expb).lhs();
        const exprt &rhs=to_binary_relation_expr(expb).rhs();

        // !(ID_le) --> ID_gt
        if(expb.id()==ID_le) {
          exprt exp=binary_relation_exprt(lhs, ID_gt, rhs);
#ifdef DEBUG
          std::cout << "The new non-negated expression is " << from_expr(exp)  << std::endl;
#endif
          mout=exp;
        }

        // !(ID_ge) --> ID_lt
        else if(expb.id()==ID_ge) {
          exprt exp=binary_relation_exprt(lhs, ID_lt, rhs);
#ifdef DEBUG
          std::cout << "The new non-negated expression is " << from_expr(exp)  << std::endl;
#endif
          mout=exp;
        }

        else if(expb.id()==ID_lt || expb.id()==ID_gt) {
          // this must not happen because
          // the expressions are now generated as <= or >=
          assert(false);
        }
      }
   } // end not
   // do not normalize if the expression is not ID_not
   else {
    assert(m.id() != ID_not);
    mout=m;
   }
}

/*******************************************************************\

Function: acdl_domaint::is_subsumed_syntactic()

  Inputs: example: 1. x<=3, 0<=x && x<=3
                   2. x<=2, 0<=x && x<=3
                   3. x<=5, 3<=x && x<=3
 Outputs: example  1: true
                   2. false
                   3. false
 Purpose: is_subsumed(a, b)==not is_strictly_contained(a, b)

          contains(a, b)==(b<=a)==((-a && b)==0)

\*******************************************************************/

bool acdl_domaint::is_subsumed_syntactic(const meet_irreduciblet &m,
                               const valuet &value) const
{
#ifdef DEBUG
  std::cout << "Subsumption test of meet irreducible " << from_expr(m) << std::endl;
#endif
  bool subsumed_check=false;
  if(value.empty()) // assumes that m is never TOP
    return false;

  // when the result of projection(m) is FALSE
  if(m.is_false())
    return false;

  // call simplifier_exprt() to simplify expressions, 
  // o/p is always of the shape !(x<=N)
  // example: (-x-y>=-N) --> !(x+y>N)
  simplify_expr(m, SSA.ns);
#ifdef DEBUG
  std::cout << "Simplified expression is " << from_expr(m) << std::endl;
#endif

  if(m.id()==ID_symbol ||
     (m.id()==ID_not && m.op0().id()==ID_symbol)
     || (m.id()==ID_not && m.op0().id()==ID_not && m.op0().op0().id()==ID_symbol)) // for (!(!(cond)))*/
  {
    
    for(unsigned i=0; i<value.size(); i++)
    {
      if(m==value[i]) {
#ifdef DEBUG
         std::cout << from_expr(m) << 
           " is subsumed by" << from_expr(value[i]) << std::endl;
#endif         
        return true;
      }
    }
    return false;
  }
  else
  { 
    // here, m must be of type ID_le or ID_ge or ID_lt or ID_gt 
    meet_irreduciblet mout, val;
    normalize_meetirrd(m, mout);
    const exprt &lhs=to_binary_relation_expr(mout).lhs();
    //const exprt &rhs=to_binary_relation_expr(mout).rhs();
    mp_integer val1, val2;
#if 0
    bool minus_val=false, minus_m=false; 
#endif
    std::vector<exprt> lhs_container;
    for(unsigned i=0; i<value.size(); i++) {
      exprt v = value[i];
      // handled these before reaching here
      if(v.id()==ID_symbol ||
        (v.id()==ID_not && v.op0().id()==ID_symbol)
        || (v.id()==ID_not && v.op0().id()==ID_not && v.op0().op0().id()==ID_symbol)) // for (!(!(cond)))*/
        continue;
     
      // normalize must return expression 
      // of the form x<N or x>N 
      normalize_meetirrd(v, val);

      // [CHECK] The constraints (x==N) must not be encountered here

      if(val == mout) {
#ifdef DEBUG
        std::cout << from_expr(mout) << 
          " is subsumed by" << from_expr(val) << std::endl;
        return true;
#endif
      }
      else { 

        assert(val.id() == ID_lt || val.id() == ID_gt || val.id() == ID_ge || val.id() == ID_le);
        const exprt &lhsv=to_binary_relation_expr(val).lhs();
        //const exprt &rhsv=to_binary_relation_expr(val).rhs();
        
        exprt lhsv_op, lhs_op;
        // Check for I/P: (-x<=10)
        // Check for val
        if(lhsv.id()==ID_unary_minus &&
            lhsv.op0().id()==ID_typecast)
        {
          lhsv_op = lhsv.op0().op0();
          // Identify negative value object
          //minus_val=true;
        }
        else
        {
          //minus_val=false;
          lhsv_op = lhsv;
        }

        // Check for m
        if(lhs.id()==ID_unary_minus &&
            lhs.op0().id()==ID_typecast)
        {
          // Identify negative meet_irreducible
          //minus_m=true;
          lhs_op = lhs.op0().op0();
        }
        else
        {
          //minus_m=false;
          lhs_op = lhs;
        }

        if(lhs_op == lhsv_op) 
        {
#ifdef DEBUG
          std::cout << "lhs matches, push into lhs container " << from_expr(val) << std::endl;
#endif
          // collect all statements with matching lhs
          lhs_container.push_back(val);


          // [IMPORTANT] Following comparison are relevant
          // Case1: val=(x<=10), m=(-x>9)
          // Case2: val=(x<=10), m=(x<=5)
          // Case3: val=(x<=10), m=(x<5)
          // Case4: val=(x>=10), m=(x>=5)
          // Case5: val=(x>=10), m=(x>5)
          // Case6: val=(x>=10), m=(-x<5)
#if 0           
          // check the subsumption for ID_gt
          if((mout.id()==ID_gt && val.id()==ID_ge) || 
              (mout.id()==ID_ge && val.id()==ID_ge) ||
              (mout.id()==ID_ge && val.id()==ID_lt && (minus_m==true))

            )

          {}
#ifdef DEBUG
          std::cout << "computing lower value" << std::endl;
#endif
          // lower bound for val
          constant_exprt cexprv=to_constant_expr(to_binary_relation_expr(val).rhs());
          to_integer(cexprv, val1);

          // lower bound for m
          constant_exprt cexprm=to_constant_expr(to_binary_relation_expr(mout).rhs());
          to_integer(cexprm, val2);

          // compare the bounds
          if(val1<val2) {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is not subsumed by" << from_expr(val) << std::endl;
#endif
            return false;
          }
          else {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is subsumed by" << from_expr(val) << std::endl;
#endif
            return true;
          }
        }

        // check the subsumption for ID_lt
        if(val.id()==ID_lt) {
#ifdef DEBUG
          std::cout << "computing upper value" << std::endl;
#endif
          // lower bound for val
          constant_exprt cexprv=to_constant_expr(to_binary_relation_expr(val).rhs());
          to_integer(cexprv, val1);

          // lower bound for m
          constant_exprt cexprm=to_constant_expr(to_binary_relation_expr(mout).rhs());
          to_integer(cexprm, val2);

          // compare the bounds
          if(val1<val2) {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is subsumed by" << from_expr(val) << std::endl;
#endif
            return true;
          }
          else {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is not subsumed by" << from_expr(val) << std::endl;
#endif
            return false;
          }
        }

        // check the subsumption for ID_le
        if(val.id()==ID_le) {
#ifdef DEBUG
          std::cout << "computing upper value" << std::endl;
#endif
          // lower bound for val
          constant_exprt cexprv=to_constant_expr(to_binary_relation_expr(val).rhs());
          to_integer(cexprv, val1);

          // lower bound for m
          constant_exprt cexprm=to_constant_expr(to_binary_relation_expr(mout).rhs());
          to_integer(cexprm, val2);

          // compare the bounds
          if(val1<val2) {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is subsumed by" << from_expr(val) << std::endl;
#endif
            return true;
          }
          else {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is not subsumed by" << from_expr(val) << std::endl;
#endif
            return false;
          }
        }

        // check the subsumption for ID_ge
        if(val.id()==ID_ge) {
#ifdef DEBUG
          std::cout << "computing lower value" << std::endl;
#endif
          // lower bound for val
          constant_exprt cexprv=to_constant_expr(to_binary_relation_expr(val).rhs());
          to_integer(cexprv, val1);

          // lower bound for m
          constant_exprt cexprm=to_constant_expr(to_binary_relation_expr(mout).rhs());
          to_integer(cexprm, val2);

          // compare the bounds
          if(val1<val2) {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is not subsumed by" << from_expr(val) << std::endl;
#endif
            return false;
          }
          else {
            subsumed_check = true;
#ifdef DEBUG
            std::cout << from_expr(mout) << 
              "is subsumed by" << from_expr(val) << std::endl;
#endif
            return true;
          }
        }
#endif
      } // end matching lhs templates
      else 
        continue;
    } // handle meet_irreducibles which are not just symbols
  } // end for loop checking all values

  // Do semantic subsumption check here
  exprt f;
  if(lhs_container.size()==0) {
#ifdef DEBUG
    std::cout << "No matching lhs found, so checking against whole value " << std::endl;
#endif
    f=simplify_expr(and_exprt(conjunction(value), not_exprt(mout)), SSA.ns);
  }
  else {
#ifdef DEBUG
   std::cout << "Actual subsumption test of meet irreducible " << from_expr(mout) 
     << " versus the value object " << from_expr(conjunction(lhs_container)) << std::endl;
#endif
   f=simplify_expr(and_exprt(conjunction(lhs_container), not_exprt(mout)), SSA.ns);
  }

  if(f.is_false())
    return true;

  bool status = semantic_subsumption(f);
  if(status) { 
#ifdef DEBUG
    std::cout << "SUBSUMPTION RESULT:: subsumed" << std::endl;
#endif
    subsumed_check=true;
    return true;
  }
  else {
#ifdef DEBUG
    std::cout << "SUBSUMPTION RESULT:: not subsumed" << std::endl;
#endif
    subsumed_check=true;
    return false;
  }
} // handle meet_irreducible m which are not just symbols
if(subsumed_check==false) {
  std::cout << "No subsumption check occured, hence return false conservatively !! " << std::endl;
  return false;
}

assert(false);
}

/*******************************************************************\

Function: acdl_domaint::semantic_subsumption()

  Inputs: example: 1. x<=3, 0<=x && x<=3
                   2. x<=2, 0<=x && x<=3
                   3. x<=5, 3<=x && x<=3
 Outputs: example  1: true
                   2. false
                   3. false
 Purpose: is_subsumed(a, b)==not is_strictly_contained(a, b)

          contains(a, b)==(b<=a)==((-a && b)==0)

\*******************************************************************/
bool acdl_domaint::semantic_subsumption(const meet_irreduciblet &m) const
{
  std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));
  *solver << m;
  if((*solver)()==decision_proceduret::D_UNSATISFIABLE)
    return true;
  else 
    return false;
}

/*******************************************************************\

Function: acdl_domaint::is_subsumed()

  Inputs: example: 1. x<=3, 0<=x && x<=3
                   2. x<=2, 0<=x && x<=3
                   3. x<=5, 3<=x && x<=3
 Outputs: example  1: true
                   2. false
                   3. false
 Purpose: is_subsumed(a, b)==not is_strictly_contained(a, b)

          contains(a, b)==(b<=a)==((-a && b)==0)

\*******************************************************************/

bool acdl_domaint::is_subsumed(const meet_irreduciblet &m,
                               const valuet &value) const
{
  if(value.empty()) // assumes that m is never TOP
    return false;

  // when the result of projection(m) is FALSE
  if(m.is_false())
    return false;

  if(m.id()==ID_symbol ||
     (m.id()==ID_not && m.op0().id()==ID_symbol))
  {
    for(unsigned i=0; i<value.size(); i++)
    {
      if(m==value[i])
        return true;
    }
    return false;
  }
  else
  {
#if 0
    // [NOTE] the following optimization 
    // leads to non-termination
    // identify the octagonal constraints
    // do not perform subsumption check 
    // for the octagonal constraints 
    exprt op;
    if(m.id()==ID_not) 
      op = m.op0();
    else 
      op = m;
    if(op.op0().id()==ID_plus || op.op0().id()==ID_minus) {
      std::cout << "Constraint is: " << m.pretty() << std::endl;
      std::cout << "Ignore Octagon constraint from Subsumption Check" << std::endl;
      return false;
    }
#endif
    // maybe the simplifier does the job
/*    exprt f=simplify_expr(and_exprt(conjunction(value),
      not_exprt(and_exprt(conjunction(value), m))), SSA.ns);*/

    exprt f1=simplify_expr(conjunction(value), SSA.ns);
    if(f1.is_false())
      return false;

    exprt f=simplify_expr(and_exprt(conjunction(value), not_exprt(m)), SSA.ns);
    if(f.is_false())
      return true;

    std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));
    *solver << f;
    if((*solver)()==decision_proceduret::D_UNSATISFIABLE)
      return true;

    return false;
  }

  assert(false);
}


/*******************************************************************\

Function: acdl_domaint::is_contained()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::is_contained(const meet_irreduciblet &m,
                                const valuet &value) const
{
  if(value.empty())
    return true;

  if(m.id()==ID_symbol ||
     (m.id()==ID_not && m.op0().id()==ID_symbol))
  {
    exprt not_m=simplify_expr(not_exprt(m), SSA.ns);
    for(unsigned i=0; i<value.size(); i++)
    {
      if(not_m==value[i])
        return false;
    }
    return true;
  }
  else
  {
    // maybe the simplifier does the job
    exprt f=simplify_expr(and_exprt(conjunction(value), not_exprt(m)), SSA.ns);
    if(f.is_false())
      return true;

    std::unique_ptr<incremental_solvert> solver(
      incremental_solvert::allocate(SSA.ns, true));
    *solver << f;
    if((*solver)()==decision_proceduret::D_UNSATISFIABLE)
      return true;

    return false;
  }

  assert(false);
}

/*******************************************************************\

Function: acdl_domaint::is_bottom()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::is_bottom(const valuet &value) const
{
  return value.size()==1 && value[0].is_false();
}


/*******************************************************************\

Function: acdl_domaint::remove_vars()

  Inputs: example:
          Old_value=(1<=x && x<=5) && (0<=y && y<=10) vars=x

 Outputs: example:
          (0<=y && y<=10)

 Purpose: TODO: this projection is quite imprecise for relational domains.

\*******************************************************************/

void acdl_domaint::remove_vars(const valuet &old_value,
                               const varst &vars,
                               valuet &new_value)
{
  for(valuet::const_iterator it=old_value.begin();
      it!=old_value.end(); ++it)
  {
    find_symbols_sett symbols;
    find_symbols(*it, symbols);
    bool found=false;
    for(varst::const_iterator v_it=vars.begin();
        v_it!=vars.end(); ++v_it)
    {
      if(symbols.find(v_it->get_identifier())!=symbols.end())
      {
        found=true;
        break;
      }
    }
    if(!found)
      new_value.push_back(*it);
  }
}

/*******************************************************************\

Function: acdl_domaint::remove_var()

  Inputs: example:
          Old_value=(1<=x && x<=5) && (0<=y && y<=10) vars=x

 Outputs: example:
          (0<=y && y<=10)

 Purpose: TODO: this projection is quite imprecise for relational domains.

\*******************************************************************/

void acdl_domaint::remove_var(const valuet &old_value,
                              const symbol_exprt &var,
                              valuet &new_value)
{
  for(valuet::const_iterator it=old_value.begin();
      it!=old_value.end(); ++it)
  {
    find_symbols_sett symbols;
    find_symbols(*it, symbols);
    if(symbols.find(var.get_identifier())==symbols.end())
      new_value.push_back(*it);
  }
}

/*******************************************************************\

Function: acdl_domaint::build_meet_irreducible_templates()

  Inputs: example: x, y

 Outputs: example for interval domain: x, y
                  for zones domain: x, y, x-y
                  for octagon domain: x, y, x-y, x+y

 Purpose:

\*******************************************************************/

void acdl_domaint::build_meet_irreducible_templates(
  const varst &vars,
  std::vector<exprt> &meet_irreducible_templates)
{
#ifdef DEBUG
  std::cout << "Building templates" << std::endl;
#endif
  template_generator_acdlt template_generator(options, ssa_db, ssa_local_unwinder);
  template_generator.set_message_handler(get_message_handler());
  template_generator(SSA, vars);
  template_generator.positive_template(meet_irreducible_templates);
}


/*******************************************************************\

Function: acdl_domaint::split()

  Inputs: example:
            expr: x-y
            value: -(x-y)<=1 && x-y<=5 && -y<=0 && y<=10 && ...
          This is very generic, can be easily extended to octagons and
          other richer domains
 Outputs: example:
            2<=x-y (for upper=true)

 Purpose: splits constant-bounded expressions in half
          If the expression is already a singleton then we cannot split
          and we return false.

\*******************************************************************/

exprt acdl_domaint::split(const valuet &value,
                          const exprt &meet_irreducible_template,
                          bool upper) const
{
  const exprt &expr=meet_irreducible_template;

  std::cout << "conjuncted value received inside split :: " << from_expr(SSA.ns, "", conjunction(value)) << std::endl;
  for(unsigned i=0;i<value.size();i++)
    std::cout << "value :: " << from_expr(SSA.ns, "", value[i]) << std::endl;
#if 0
// #ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] Split("
            << from_expr(SSA.ns, "", meet_irreducible_template) << "): "; output(std::cout, value);
  std::cout << "" << std::endl;
#endif

  if(expr.type().id()==ID_bool)
  {
    exprt v_true=simplify_expr(and_exprt(conjunction(value), expr), SSA.ns);
#ifdef DEBUG
    std::cout << "v_true: "
              << from_expr(SSA.ns, "", v_true)
              << std::endl;
#endif
    if(v_true.is_false())
      return false_exprt();
    exprt v_false=simplify_expr(and_exprt(conjunction(value),
                                          not_exprt(expr)), SSA.ns);
#ifdef DEBUG
    std::cout << "v_false: "
              << from_expr(SSA.ns, "", v_false)
              << std::endl;
#endif
    if(v_false.is_false())
      return false_exprt();
    if(upper)
      return expr;
    else
      return not_exprt(expr);
  }

  if(!(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_floatbv))
  {
    std::cout << "WARNING: do not know how to split "
              << from_expr(SSA.ns, "", expr)
              << " of type " << from_type(SSA.ns, "", expr.type())
              << std::endl;
    return false_exprt();
  }

  // match template expression

  // preprocess the elements in v to remove negation
  // Example: I/P: !(x<=10) --> O/P: (x>=10)
  std::vector<meet_irreduciblet> new_value;
  for(unsigned i=0; i<value.size(); i++)
  {
    const exprt &e=value[i];
    // check for expression with negations (ex- !(x<=10) or !(x>=10))
    if(e.id()==ID_not) {
#ifdef DEBUG
      std::cout << "The original not expression is " << from_expr(e) << std::endl;
#endif
      const exprt &expb=e.op0();

      // Handle the singleton case: example : !guard#0
      if(expb.id()!=ID_le && expb.id()!=ID_ge)
      {
        new_value.push_back(expb);
        continue;
      }
      const exprt &lhs=to_binary_relation_expr(expb).lhs();
      const exprt &rhs=to_binary_relation_expr(expb).rhs();
      if(expb.id()==ID_le) {
        // !(ID_le) --> ID_gt
        exprt exp=binary_relation_exprt(lhs, ID_gt, rhs);
#ifdef DEBUG
        std::cout << "The new non-negated expression is " << from_expr(exp)  << std::endl;
#endif
        new_value.push_back(exp);
      }
      // !(ID_ge) --> ID_lt
      else if(expb.id()==ID_ge) {
        exprt exp=binary_relation_exprt(lhs, ID_lt, rhs);
#ifdef DEBUG
        std::cout << "The new non-negated expression is " << from_expr(exp)  << std::endl;
#endif
        new_value.push_back(exp);
      }
      else if(expb.id()==ID_lt || expb.id()==ID_gt) {
        // this must not happen because
        // the expressions are now generated as<=or >=
        assert(false);
      }
    } // end not
    // simply copy the value[i] to new_value[i]
    else {
      new_value.push_back(value[i]);
    }
  }
  // check the size of new_value and value is same here
  assert(new_value.size()==value.size());

  exprt vals=conjunction(new_value);
#ifdef DEBUG
  std::cout << "conjuncted new value:: " << from_expr(SSA.ns, "", vals) << std::endl;
  std::cout << "original splitting expr is :: " << from_expr(SSA.ns, "", expr) << std::endl;

  //std::cout << "conjuncted new value computed inside split:: " << from_expr(SSA.ns, "", conjunction(new_value)) << std::endl;
  for(unsigned i=0;i<value.size();i++)
    std::cout << "value :: " << from_expr(SSA.ns, "", value[i]) << std::endl;
#endif
  
  // computer lower and upper bound
  // handle the positive literals
  constant_exprt u;
  bool u_is_assigned=false;
  constant_exprt l;
  bool l_is_assigned=false;
  mp_integer val1, val2;
  // I/P: (x>=0 && x<=10) O/P: l=0, u=10
  for(unsigned i=0; i<new_value.size(); i++)
  {
    const exprt &e=new_value[i];
    // Handle the singleton case: example : !guard#0
    if(e.id()!=ID_le && e.id()!=ID_ge && e.id()!=ID_lt && e.id()!=ID_gt)
      continue;
    if(to_binary_relation_expr(e).lhs()==expr)
    {
      if(e.id()==ID_le)
      {
        u=to_constant_expr(to_binary_relation_expr(e).rhs());
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the upper value is "
                  << from_expr(SSA.ns, "", u) << std::endl;
#endif
        u_is_assigned=true;
        // break;
      }
      if(e.id()==ID_ge)
      {
        l=to_constant_expr(to_binary_relation_expr(e).rhs());
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        l_is_assigned=true;
        // break;
      }
      if(e.id()==ID_lt) {
#ifdef DEBUG
        std::cout << "computing upper value" << std::endl;
#endif
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, val1);
        val2=val1-1;
        u=from_integer(val2, expr.type());
        u_is_assigned=true;
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the upper value is "
                  << from_expr(SSA.ns, "", u) << std::endl;
#endif
        // break;
      }
      if(e.id()==ID_gt) {
#ifdef DEBUG
        std::cout << "computing lower value" << std::endl;
#endif
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, val1);
        val2=val1+1;
        l=from_integer(val2, expr.type());
        l_is_assigned=true;
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        // break;
      }
#if 0
      // handle ID_equality
      if(e.id()==ID_eq) {
#ifdef DEBUG
        std::cout << "computing lower value" << std::endl;
#endif
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, val1);
        val2=val1;
        l=from_integer(val2, expr.type());
        u=from_integer(val2, expr.type());
        l_is_assigned=true;
        u_is_assigned=true;

#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        // break;
      }
#endif
    }
  }

  // handle the negative literals
  mp_integer neg, cneg;
  mp_integer negu, cnegu;
  for(unsigned i=0; i<new_value.size(); i++)
  {
    const exprt &e=new_value[i];
    // Handle the singleton case: example : !guard#0
    if(e.id()!=ID_le && e.id()!=ID_ge && e.id()!=ID_lt && e.id()!=ID_gt)
      continue;
    const exprt &lhs=to_binary_relation_expr(e).lhs();
    if(lhs.id()==ID_unary_minus &&
       lhs.op0().id()==ID_typecast &&
       lhs.op0().op0()==expr)
    {
      // I/P: (-x<=10) O/P: l=-10
      if(e.id()==ID_le) {
        const exprt &rhs=to_binary_relation_expr(e).rhs();
        constant_exprt cexpr=to_constant_expr(rhs);
        to_integer(cexpr, neg);
        cneg=-neg;
        l=from_integer(cneg, expr.type());
        l_is_assigned=true;
        // break;
      }
      // I/P: (-x >= 10) O/P: u=-10
      if(e.id()==ID_ge) {
        const exprt &rhs=to_binary_relation_expr(e).rhs();
        constant_exprt cexpru=to_constant_expr(rhs);
        to_integer(cexpru, negu);
        cnegu=-negu;
        u=from_integer(cnegu, expr.type());
        u_is_assigned=true;
        // break;
      }
      // I/P: (-x<10) O/P: l=(-10+1)=-9
      if(e.id()==ID_lt) {
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, neg);
        cneg=(-neg)+1;
        l=from_integer(cneg, expr.type());
        l_is_assigned=true;
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        // break;
      }
      // I/P: (-x > 10) O/P: l=(-10-1)=-11
      if(e.id()==ID_gt) {
        constant_exprt cexpru=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpru, negu);
        cnegu=(-negu)-1;
        u=from_integer(cnegu, expr.type());
        u_is_assigned=true;
        // break;
      }
    }
  }

  if(!u_is_assigned && !l_is_assigned) {
#ifdef DEBUG
    std::cout << "Decision variable not present in the abstract value" << std::endl;
#endif
  }

  if(!u_is_assigned)
  {
    u=tpolyhedra_domaint::get_max_value(expr);
  }
  if(!l_is_assigned)
  {
    l=tpolyhedra_domaint::get_min_value(expr);
  }


  // TODO: check whether we have a singleton, then we cannot split anymore
  if (l==u)
    return false_exprt();

  exprt m=tpolyhedra_domaint::between(l, u);

#ifdef DEBUG
  std::cout << "[ACDL DOMAIN] expr: " << from_expr(SSA.ns, "", expr)
            << "[ACDL DOMAIN] min: "
            << from_expr(SSA.ns, "", l)
            << "[ACDL DOMAIN] max: "
            << from_expr(SSA.ns, "", u)
            << "[ACDL DOMAIN] mid: "
            << from_expr(SSA.ns, "", m) << std::endl;
#endif
  if(upper)
  {
#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] decision: "
              << from_expr(SSA.ns, "", binary_relation_exprt(m, ID_le, expr)) << std::endl;
#endif
    return binary_relation_exprt(m, ID_le, expr);
  }
  else
  {
#ifdef DEBUG
    std::cout << "[ACDL-DOMAIN] decision: "
              << from_expr(SSA.ns, "", binary_relation_exprt(expr, ID_le, m)) << std::endl;
#endif
    return binary_relation_exprt(expr, ID_le, m);
  }
  return false_exprt();
}


/*******************************************************************\

Function: acdl_domaint::remove_expr()

  Inputs: example:
          Old_value=(1<=x && x<=5) && (0<=y && y<=10)
          expr=(1<=x)

 Outputs: example:
          (x<=5) && (0<=y && y<=10)

 Purpose:

\*******************************************************************/

void acdl_domaint::remove_expr(valuet &old_value,
                               exprt &expr,
                               valuet &new_value)
{
  for(valuet::const_iterator it=old_value.begin();
      it!=old_value.end(); ++it)
  {
    if(expr==*it) {
#ifdef DEBUG
      std::cout << "[ACDL-DOMAIN] REMOVE EXPR: "
                << from_expr(SSA.ns, "", expr) << std::endl
                << "[ACDL-DOMAIN] MATCHED VALUE: "
                << from_expr(SSA.ns, "", *it) << std::endl;
#endif
      continue;
    }
    else
      new_value.push_back(*it);
  }

#if 0
  std::set<symbol_exprt> var;
  // find all variables in a statement
  find_symbols (expr, var);
  for(valuet::const_iterator it=old_value.begin();
      it!=old_value.end(); ++it)
  {
    find_symbols_sett symbols;
    find_symbols(*it, symbols);
    for(varst::const_iterator it1=var.begin();
        it1!=var.end(); ++it1) {
      if(symbols.find(it1->get_identifier())!=symbols.end() && expr!=*it && it->id()!=ID_not)
        new_value.push_back(*it);
    }
  }
#endif
}

/*******************************************************************\

 Function: acdl_domaint::normalize_val_syntactic()

 Inputs: (x<=5) && (x<=10) && (y<=3)

 Outputs: (x<=5) && (y<=3)

 Purpose: Normalization is value-preserving operation.

\*******************************************************************/
void acdl_domaint::normalize_val_syntactic(valuet &value)
{
#ifdef DEBUG
  std::cout << "Inside Normalize Value" << std::endl;
  std::cout << "The trail before syntactic normalizing is " << std::endl;  
  std::cout << "Printing the value inside normalization" << std::endl;
  for(unsigned i=0;i<value.size();i++)
    std::cout << from_expr(value[i]) << ", " << std::endl;
#endif
  valuet val;
  if(value.empty())
    return;
  for(unsigned i=0; i<value.size(); i++)
  {
    exprt m=value[i];
    simplify_expr(m, SSA.ns);
    
    // for expressions like !guard22
    if(m.id()==ID_symbol ||
        (m.id()==ID_not && m.op0().id()==ID_symbol) ||
        (m.id()==ID_not && m.op0().id()==ID_not && m.op0().op0().id()==ID_symbol)) // for (!(!(cond)))*/
    {
      val.push_back(m);
      continue;
    }
    else
    {
#if 0
      // identify the octagonal constraints
      // do not normalize the octagonal constraints 
      exprt op;
      if(m.id()==ID_not) 
        op = m.op0();
      else 
        op = m;
      if(op.op0().id()==ID_plus || op.op0().id()==ID_minus) {
        //std::cout << "Constraint is: " << m.pretty() << std::endl;
        // push octagonal constraints 
        val.push_back(m);
#ifdef DEBUG
        std::cout << "--> Octagon constraint, added" << std::endl;
#endif
        continue;
      }
      // normalize for interval constraints 
      else 
      { 
#endif
        valuet new_val;
        remove_expr(value, m, new_val);
#ifdef DEBUG
        std::cout << "[ACDL-DOMAIN] remove_expr: " << from_expr(SSA.ns, "", m) << std::endl;
#endif
        // preprocess val in case it contains
        // ID_equality. Subsumption only allows 
        // ID_lt, ID_gt, ID_le,  ID_ge constraints
        preprocess_val(new_val);
        if(!is_subsumed_syntactic(m, new_val))
          val.push_back(m);
      //}
    }
  }
  // delete old elements in value
  for(std::size_t i=0; i<value.size(); i++)
    value.erase(value.begin(), value.end());
  // load val in to value
  for(unsigned i=0; i<val.size(); i++)
    value.push_back(val[i]);
  
#ifdef DEBUG
  std::cout << "The trail after syntactic normalizing is " << std::endl;  
  std::cout << "Printing the normalized value inside normalization" << std::endl;
  for(unsigned i=0;i<value.size();i++)
    std::cout << from_expr(value[i]) << ", " << std::endl;
#endif  
}

/*******************************************************************\

 Function: acdl_domaint::normalize_val()

 Inputs: (x<=5) && (x<=10) && (y<=3)

 Outputs: (x<=5) && (y<=3)

 Purpose: Normalization is value-preserving operation.

\*******************************************************************/

void acdl_domaint::normalize_val(valuet &value)
{
#ifdef DEBUG
  std::cout << "Inside Normalize Value" << std::endl;
  std::cout << "The trail before normalizing is " << std::endl;  
  std::cout << "Printing the value inside normalization" << std::endl;
  for(unsigned i=0;i<value.size();i++) {
    std::cout << from_expr(value[i]) << ", " << std::endl;
    std::cout << value[i].pretty() << ", " << std::endl;
  }
#endif
  valuet val;
  if(value.empty())
    return;
  for(unsigned i=0; i<value.size(); i++)
  {
    exprt m=value[i];
#ifdef DEBUG
    //std::cout << "Checking " << from_expr(SSA.ns, "", m);
#endif
    // for expressions like !guard22
    if(m.id()==ID_symbol ||
       (m.id()==ID_not && m.op0().id()==ID_symbol))
    {
#if 0
      exprt not_m=simplify_expr(not_exprt(m), SSA.ns);
      for(unsigned i=0; i<value.size(); i++)
      {
        if(not_m==value[i])
          return false;
      }
#endif
      val.push_back(m);
#ifdef DEBUG
      std::cout << "--> Normal symbol, added" << std::endl;
#endif      
      continue;
    }
    else
    {
      // identify the octagonal constraints
      // do not normalize the octagonal constraints 
      exprt op;
      if(m.id()==ID_not) 
        op = m.op0();
      else 
        op = m;
      if(op.op0().id()==ID_plus || op.op0().id()==ID_minus) {
        //std::cout << "Constraint is: " << m.pretty() << std::endl;
        // push octagonal constraints 
        val.push_back(m);
        std::cout << "--> Octagon constraint, added" << std::endl;
        continue;
      }
      valuet new_val;
      remove_expr(value, m, new_val);
      // maybe the simplifier does the job
      exprt f1=and_exprt(conjunction(new_val), not_exprt(m));
      exprt f=simplify_expr(and_exprt(conjunction(new_val), not_exprt(m)), SSA.ns);
#ifdef DEBUG
      std::cout << "[ACDL-DOMAIN] remove_expr: " << from_expr(SSA.ns, "", m) << "SAT query without simplifiert: "
                << from_expr(SSA.ns, "", f1) << std::endl;
#endif
      if(f.is_false()) {
#ifdef DEBUG
        std::cout << "--> negation is false, ignored" << std::endl;
#endif
        continue;
      }
      bool result=check_val(f);
#ifdef DEBUG
      std::cout << "[ACDL-DOMAIN] SAT result: ";
#endif
      // check if UNSAT
      if(result) {
#ifdef DEBUG
        std::cout << "UNSAT " << std::endl;
        std::cout << "--> UNSAT, ignored" << std::endl;
#endif
        continue;
      }
      // if satisfiable, then push into val
      else {
#ifdef DEBUG
        std::cout << "SAT " << std::endl;
        std::cout << "--> SAT, added" << std::endl;
#endif
        val.push_back(m);
      }
    }
  }
  // delete old elements in value
  for(unsigned i=0; i<value.size(); i++)
    value.erase(value.begin(), value.end());
  // load val in to value
  for(unsigned i=0; i<val.size(); i++)
    value.push_back(val[i]);
  
#ifdef DEBUG
  std::cout << "The trail after normalizing is " << std::endl;  
  std::cout << "Printing the normalized value inside normalization" << std::endl;
  for(unsigned i=0;i<value.size();i++)
    std::cout << from_expr(value[i]) << ", " << std::endl;
#endif  
}

/*******************************************************************\

Function: acdl_domaint::normalize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void acdl_domaint::normalize(valuet &value)
{
  for(unsigned i=0; i<value.size(); i++)
  {
    if(value[i].is_false())
    {
      set_bottom(value);
      return;
    }
  }

#if 0
  // I don't think this is needed anymore
  else {
    exprt old_value=value[i];

    std::vector<symbol_exprt> clean_vars;
    valuet new_value;
    // project out vars
    for(varst::const_iterator it=vars.begin();
        it!=vars.end(); ++it)
    {
      // we only normalize what the abstract domain currently handles
      if(it->type().id()==ID_signedbv ||
         it->type().id()==ID_unsignedbv ||
         it->type().id()==ID_floatbv)
      {
        remove_var(value, *it, new_value);
        clean_vars.push_back(*it);
      }
    }

    ssa_analyzert ssa_analyzer;
    std::unique_ptr<incremental_solvert> solver(incremental_solvert::allocate(SSA.ns, true));

    template_generator_acdlt template_generator(options, ssa_db, ssa_local_unwinder);
    template_generator(SSA, clean_vars);

    ssa_analyzer(*solver, SSA, old_value, template_generator);
    exprt new_values;
    ssa_analyzer.get_result(new_values, template_generator.all_vars());

    for(unsigned k=0; k<new_value.size(); k++)
      value.push_back(and_exprt(new_values, new_value[k]));
  } // end of else
} // end for
#endif
}


/*******************************************************************\

Function: acdl_domaint::check_val()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::check_val(const exprt &expr)
{
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
#ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] original SAT query: " << from_expr(SSA.ns, "", expr)
            << std::endl;
#endif
  *solver << expr;
  decision_proceduret::resultt result=(*solver)();
#ifdef DEBUG
  std::cout << "original SAT result: " << result << std::endl;
#endif
  if(result==decision_proceduret::D_UNSATISFIABLE) {
#ifdef DEBUG
    std::cout<< "UNSAT" << std::endl;
#endif
    return true;
  }
  else {
#ifdef DEBUG
    std::cout<< "SAT" << std::endl;
#endif
    return false;
  }
}


/*******************************************************************\

Function: acdl_domaint::expr_to_value()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::expr_is_true(const exprt &expr)
{
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  *solver << not_exprt(expr);
  return ((*solver)()==decision_proceduret::D_UNSATISFIABLE);
}

void acdl_domaint::expr_to_value(const exprt &expr, valuet &value)
{
  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      expr_to_value(*it, value);
  }
  else
  {
    if(!expr_is_true(expr))
    {
      value.push_back(expr);
    }
  }
}

/*******************************************************************\

Function: acdl_domaint::compare()

  Inputs: example: 1. x<=3, x<=5 && y<=10
                   2. x<=2, x>2 && y<=10
                   3. x<=5, x>=3 && x<=8 && y<=10
 Outputs: example  1: satisfiable (status=0)
                   2. contradicting (status=1)
                   3. unknown -- neither satisfiable nor contradicting (status=2)
\*******************************************************************/

unsigned acdl_domaint::compare(const meet_irreduciblet &a,
                               const meet_irreduciblet &b) const
{
  exprt f=simplify_expr(and_exprt(a, b), SSA.ns);
  if(f.is_false())
    return CONFLICT;

  std::unique_ptr<incremental_solvert> solver1(
    incremental_solvert::allocate(SSA.ns, true));
  // to check contradiction, check (a & b) is UNSAT
  *solver1 << and_exprt(a, b);
  if ((*solver1)()==decision_proceduret::D_UNSATISFIABLE) {
    return CONFLICT;
  }

  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  // to check satisfiable, check !(a & !b)
  *solver << not_exprt(and_exprt(a, not_exprt(b)));
  if ((*solver)()==decision_proceduret::D_UNSATISFIABLE) {
    return SATISFIED;
  }
  // unknown: neither contradicting nor satisfiable
  else {
    return UNKNOWN;
  }
}


/*******************************************************************\

Function: acdl_domaint::compare_val_lit()

  Inputs: example: 1. val:x<=5 && y<=10 lit:x<=10
                   2. val:x<=2 && y<=10 lit:x>2
                   3. val:x>=3 && x<=8 && y<=10 lit:x<=5
 Outputs: example  1: satisfiable
                   2. contradicting
                   3. unknown -- neither satisfiable nor contradicting
\*******************************************************************/

unsigned acdl_domaint::compare_val_lit(valuet &a,
                                       meet_irreduciblet &b)
{
  unsigned int status;

  exprt f=simplify_expr(and_exprt(conjunction(a), (b)), SSA.ns);
  if(f.is_false())
    return CONFLICT;

  std::unique_ptr<incremental_solvert> solver1(
    incremental_solvert::allocate(SSA.ns, true));
  // to check contradiction, check (a & b) is UNSAT
  *solver1 << and_exprt(conjunction(a), b);
  if ((*solver1)()==decision_proceduret::D_UNSATISFIABLE) {
    status=0;
    return status; // CONFLICT;
  }

  // to check satisfiable,
  // forall a, b, a=>b is SAT
  // Exists a, b, !(a=>b) is UNSAT
  // check (a && !b) is UNSAT
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  *solver << and_exprt(conjunction(a), not_exprt(b));
  if ((*solver)()==decision_proceduret::D_UNSATISFIABLE) {
    status=2;
    return status; // SATISFIED;
  }
  // unknown: neither contradicting nor satisfiable
  else {
    status=1;
    return status; // UNKNOWN;
  }
}

/*******************************************************************\

Function: acdl_domaint::check_abstract_value()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::check_val_consistency(valuet &val)
{
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
#ifdef DEBUG
  std::cout << "Checking consistency for value " <<
    from_expr(SSA.ns, "", conjunction(val)) << std::endl;
#endif
  *solver << conjunction(val);
  decision_proceduret::resultt res=(*solver)();
  if(res==decision_proceduret::D_UNSATISFIABLE)
    return false;
  else
    return true;
}

/*******************************************************************\

Function: acdl_domaint::check_abstract_value()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool acdl_domaint::check_val_satisfaction(valuet &val)
{
#ifdef DEBUG
  std::cout << "Checking satisfaction for value " << from_expr(SSA.ns, "", conjunction(val)) << std::endl;
#endif
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  *solver << conjunction(val);
  decision_proceduret::resultt res=(*solver)();
  if(res==decision_proceduret::D_SATISFIABLE)
    return true;
  else
    return false;
}

/*******************************************************************\

Function: acdl_domaint::check_contradiction()

  Inputs:

 Outputs:

 Purpose: if contradict, return true else return false

\*******************************************************************/

bool acdl_domaint::check_contradiction(valuet &val, exprt &expr)
{
  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  exprt result=and_exprt(conjunction(val), expr);
  *solver << result;
  decision_proceduret::resultt res=(*solver)();
  if(res==decision_proceduret::D_UNSATISFIABLE)
    return true;
  else
    return false;
}

/*******************************************************************\

Function: acdl_domaint::unit_rule

 Case 1:
 Abstract value: (x:[5, 10] && y:[20:30] && z:[6, 18])
 Clause: (x<3 V y>50 V z<10) -- UNIT clause
 Here, x<3, y>50 -- contradicted literal, z<10 -- unit literal
 Deductions made after unit rule: (z<10)
 Abstract Value: (x:[5, 10] && y:[20:30] && z:[6, 9])

 Case 2:
 Abstract value:  ($x \in [5, 13]$, $y \in [-2, 9]$)
 Clause: (x<4 \vee y>10 \vee z<15)
 Deduction after application of unit rule: z<15
 New abstract value: ($x \in [5, 13]$,  $y \in [-2, 9]$,  $z \in [-INF, 14]$)

 Case 3:
 Abstract value (x > 5, y<20, z > 5).
 Clause: $C=(x<3 \vee y>50 \vee z<10)$
 Here, the literals x<3 and y>50 are contradicting. And z<10 is UNKNOWN, so
 the clause is UNIT. Unit literal is z<10.
 Deduction after application of unit rule: meet(z>5, z<10) --> z:[6, 9]
 Abstract value: ($x \in [5, 13]$,  $y \in [-2, 9]$, $z \in [6, 9]$).

 Purpose:

\*******************************************************************/
int acdl_domaint::unit_rule(const local_SSAt &SSA, valuet &v, valuet &clause, exprt &unit_lit)
{
  assert(check_val_consistency(v));
  // Normalize the current partial assignment
  normalize(v);
  int unit_idx=-1;
  unsigned i=0;
  bool disjoint=false;
  bool new_lit=false;
#ifdef DEBUG
  std::cout << "Checking unit rule for the clause " << from_expr(SSA.ns, "", disjunction(clause)) << std::endl;
#endif

  for(i=0;i<clause.size();i++)
  {
    acdl_domaint::valuet relevant_expr;
    disjoint=false;
    new_lit=false;
    exprt clause_exp=clause[i];
#ifdef DEBUG
    std::cout << "comparing " << from_expr(SSA.ns, "", conjunction(v)) << " <---> " << from_expr(SSA.ns, "", clause_exp) << std::endl;
#endif
    // check symbols in clause_exp with that of v
    acdl_domaint::varst exp_symbols;
    find_symbols(clause_exp, exp_symbols);
    new_lit=true;
    // check over all abstract value
    for(acdl_domaint::valuet::iterator it=v.begin();
        it!=v.end(); ++it)
    {
      acdl_domaint::varst v_symbol;
      find_symbols(*it, v_symbol);
      for(acdl_domaint::varst::iterator it1=v_symbol.begin(); it1!=v_symbol.end(); it1++) {
        bool is_in=exp_symbols.find(*it1)!=exp_symbols.end();

        if(is_in) {
          // push relevant expr into container
          relevant_expr.push_back(*it);
          new_lit=false;
        }
      }
    }
    // got new literal in clause
    // which is not present in abstract value
    if(new_lit) {
      unit_idx=i;
      continue;
    }

    // now set up for actual comparisons
    // since there are overlap of symbols
    // between the abstract value and clause
#ifdef OCTAGONS
    // for octagons, compare with the whole abstract
    // value since there can be transitive dependencies
    // between the octagonal constraints
    int status=compare_val_lit(v, clause_exp);
#else
#ifdef DEBUG
    std::cout << "Comparing relevant expressions " << from_expr(SSA.ns, "", conjunction(relevant_expr)) << " <---> " << from_expr(SSA.ns, "", clause_exp) << std::endl;
#endif
    // for intervals, we can select relevant
    // variables in the abstract value
    int status=compare_val_lit(relevant_expr, clause_exp);
#endif

#ifdef DEBUG
    std::cout << "The status is " << status << std::endl;
#endif
    if(status==SATISFIED)
      return SATISFIED;
    if(status!=CONFLICT) // not CONTRADICTED
    {
      // if its not contradicted
      if(unit_idx!=-1)
        return UNKNOWN; // we have more than one uncontradicted literals
      unit_idx=i;
    }
    else
    {
      disjoint=true;
    }
  }

  // check for clause with size 1 which
  // does not have a matching literal
  // in the abstract value, so they are unit by default
  // *******************************************************************
  // Example: Input: val:(x<10 V y>10) clause:cond21
  //         Output: deduction:(cond21), return that the clause is UNIT
  // *******************************************************************

  if(!disjoint && new_lit)
  {
#ifdef DEBUG
    std::cout << "CLAUSE IS UNIT" << std::endl;
#endif
    // clause is unit
    unit_lit=clause[unit_idx];

#ifdef DEBUG
    std::cout << "The unit literal is " << from_expr(SSA.ns, "", unit_lit) << std::endl;
#endif
    return UNIT;
  }

  if(unit_idx==-1)
  {
#ifdef DEBUG
    std::cout << "CLAUSE IS IN CONFLICT" << std::endl;
#endif
    // conflicting_clause=learned_clauses.size()-1;
    return CONFLICT;
  }

#ifdef DEBUG
  std::cout << "CLAUSE IS UNIT" << std::endl;
  std::cout << "The unit literal index is " << unit_idx << std::endl;
#endif
  // clause is unit
  unit_lit=clause[unit_idx];
#ifdef DEBUG
  std::cout << "The unit literal is " << from_expr(SSA.ns, "", unit_lit) << std::endl;
#endif
  return UNIT; // UNIT clause
}

/*******************************************************************\

Function: acdl_domaint::get_var_bound()

  Inputs:

  Outputs:

  Purpose: works for intervals and octagons
           (x>=10 && x<=15) --> l=10, u=20
           (x+y >= 10 && x+y<=15) --> l=10, u=20

\*******************************************************************/

std::pair<mp_integer, mp_integer> acdl_domaint::get_var_bound(const valuet &value,
                                                              const exprt &expr)
{
  // const exprt &expr=meet_irreducible_template;
#ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] Get var bound("
            << from_expr(SSA.ns, "", expr) << "): "; output(std::cout, value);
  std::cout << "" << std::endl;
#endif

  typedef std::pair<mp_integer, mp_integer> val_pairt;
  val_pairt val_pair;

  if(expr.type().id()==ID_bool)
  {
    // variable bound not needed
    // for boolean variables
    mp_integer l=-1;
    mp_integer u=-1;
    val_pair.first=l;
    val_pair.second=u;
#ifdef DEBUG
    std::cout <<  "The val pair for " << from_expr(SSA.ns, "", expr) <<  "is" << "lower" << l << "upper" << u << std::endl;
#endif
    return val_pair;
  }

  if(!(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv ||
       expr.type().id()==ID_floatbv))
  {
    std::cout << "WARNING: do not know how to split "
              << from_expr(SSA.ns, "", expr)
              << " of type " << from_type(SSA.ns, "", expr.type())
              << std::endl;
    return val_pair;
  }

  // match template expression

  // preprocess the elements in v to remove negation
  // Example: I/P: !(x<=10) --> O/P: (x>=10)
  std::vector<meet_irreduciblet> new_value;
  for(unsigned i=0; i<value.size(); i++)
  {
    const exprt &e=value[i];
    // check for expression with negations (ex- !(x<=10) or !(x>=10))
    if(e.id()==ID_not) {
#ifdef DEBUG
      std::cout << "The original not expression is " << from_expr(e) << std::endl;
#endif
      const exprt &expb=e.op0();

      // Handle the singleton case: example : !guard#0
      if(expb.id()!=ID_le && expb.id()!=ID_ge)
      {
        new_value.push_back(expb);
        continue;
      }
      const exprt &lhs=to_binary_relation_expr(expb).lhs();
      const exprt &rhs=to_binary_relation_expr(expb).rhs();
      if(expb.id()==ID_le) {
        // !(ID_le) --> ID_gt
        exprt exp=binary_relation_exprt(lhs, ID_gt, rhs);
#ifdef DEBUG
        std::cout << "The new non-negated expression is " << from_expr(exp)  << std::endl;
#endif
        new_value.push_back(exp);
      }
      // !(ID_ge) --> ID_lt
      else if(expb.id()==ID_ge) {
        exprt exp=binary_relation_exprt(lhs, ID_lt, rhs);
#ifdef DEBUG
        std::cout << "The new non-negated expression is " << from_expr(exp)  << std::endl;
#endif
        new_value.push_back(exp);
      }
      else if(expb.id()==ID_lt || expb.id()==ID_gt) {
        // this must not happen because
        // the expressions are now generated as<=or >=
        assert(false);
      }
    } // end not
    // simply copy the value[i] to new_value[i]
    else {
      new_value.push_back(value[i]);
    }
  }
  // check the size of new_value and value is same here
  assert(new_value.size()==value.size());

  exprt vals=conjunction(new_value);
#ifdef DEBUG
  std::cout << "conjuncted new value:: " << from_expr(SSA.ns, "", vals) << std::endl;
  std::cout << "original splitting expr is :: " << from_expr(SSA.ns, "", expr) << std::endl;
#endif

  // computer lower and upper bound
  // handle the positive literals
  constant_exprt u;
  bool u_is_assigned=false;
  constant_exprt l;
  bool l_is_assigned=false;
  mp_integer val1, val2;
  // I/P: (x>=0 && x<=10) O/P: l=0, u=10
  for(unsigned i=0; i<new_value.size(); i++)
  {
    const exprt &e=new_value[i];
    // Handle the singleton case: example : !guard#0
    if(e.id()!=ID_le && e.id()!=ID_ge && e.id()!=ID_lt && e.id()!=ID_gt)
      continue;
    if(to_binary_relation_expr(e).lhs()==expr)
    {
      if(e.id()==ID_le)
      {
        u=to_constant_expr(to_binary_relation_expr(e).rhs());
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the upper value is "
                  << from_expr(SSA.ns, "", u) << std::endl;
#endif
        u_is_assigned=true;
        // break;
      }
      if(e.id()==ID_ge)
      {
        l=to_constant_expr(to_binary_relation_expr(e).rhs());
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        l_is_assigned=true;
        // break;
      }
      if(e.id()==ID_lt) {
#ifdef DEBUG
        std::cout << "computing upper value" << std::endl;
#endif
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, val1);
        val2=val1-1;
        u=from_integer(val2, expr.type());
        u_is_assigned=true;
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the upper value is "
                  << from_expr(SSA.ns, "", u) << std::endl;
#endif
        // break;
      }
      if(e.id()==ID_gt) {
#ifdef DEBUG
        std::cout << "computing lower value" << std::endl;
#endif
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, val1);
        val2=val1+1;
        l=from_integer(val2, expr.type());
        l_is_assigned=true;
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        // break;
      }
    }
  }

  // handle the negative literals
  mp_integer neg, cneg;
  mp_integer negu, cnegu;
  for(unsigned i=0; i<new_value.size(); i++)
  {
    const exprt &e=new_value[i];
    // Handle the singleton case: example : !guard#0
    if(e.id()!=ID_le && e.id()!=ID_ge && e.id()!=ID_lt && e.id()!=ID_gt)
      continue;
    const exprt &lhs=to_binary_relation_expr(e).lhs();
    if(lhs.id()==ID_unary_minus &&
       lhs.op0().id()==ID_typecast &&
       lhs.op0().op0()==expr)
    {
      // I/P: (-x<=10) O/P: l=-10
      if(e.id()==ID_le) {
        const exprt &rhs=to_binary_relation_expr(e).rhs();
        constant_exprt cexpr=to_constant_expr(rhs);
        to_integer(cexpr, neg);
        cneg=-neg;
        l=from_integer(cneg, expr.type());
        l_is_assigned=true;
        // break;
      }
      // I/P: (-x >= 10) O/P: u=-10
      if(e.id()==ID_ge) {
        const exprt &rhs=to_binary_relation_expr(e).rhs();
        constant_exprt cexpru=to_constant_expr(rhs);
        to_integer(cexpru, negu);
        cnegu=-negu;
        u=from_integer(cnegu, expr.type());
        u_is_assigned=true;
        // break;
      }
      // I/P: (-x<10) O/P: l=(-10+1)=-9
      if(e.id()==ID_lt) {
        constant_exprt cexpr=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpr, neg);
        cneg=(-neg)+1;
        l=from_integer(cneg, expr.type());
        l_is_assigned=true;
#ifdef DEBUG
        std::cout << "the expression is " << from_expr(SSA.ns, "", e) << "the lower value is "
                  << from_expr(SSA.ns, "", l) << std::endl;
#endif
        // break;
      }
      // I/P: (-x > 10) O/P: l=(-10-1)=-11
      if(e.id()==ID_gt) {
        constant_exprt cexpru=to_constant_expr(to_binary_relation_expr(e).rhs());
        to_integer(cexpru, negu);
        cnegu=(-negu)-1;
        u=from_integer(cnegu, expr.type());
        u_is_assigned=true;
        // break;
      }
    }
  }

  if(!u_is_assigned && !l_is_assigned) {
#ifdef DEBUG
    std::cout << "Decision variable not present in the abstract value" << std::endl;
#endif
  }

  if(!u_is_assigned)
  {
    u=tpolyhedra_domaint::get_max_value(expr);
  }
  if(!l_is_assigned)
  {
    l=tpolyhedra_domaint::get_min_value(expr);
  }

  mp_integer upper, lower;
  to_integer(to_constant_expr(u), upper);
  to_integer(to_constant_expr(l), lower);

  val_pair.first=lower;
  val_pair.second=upper;
#ifdef DEBUG
  std::cout <<  "The val pair for " << from_expr(SSA.ns, "", expr) <<  "is" << "lower" << lower << "upper" << upper << std::endl;
#endif
  return val_pair;
}

/*******************************************************************\

Function: acdl_domaint::is_complete()

  Inputs:

 Outputs:

 Purpose: This is a very stupid and restrictive gamma-completeness check

\*******************************************************************/

bool acdl_domaint::is_complete(const valuet &value,
                               const std::set<symbol_exprt> &symbols,
                               const std::set<symbol_exprt> &ngc,
                               const exprt &ssa_conjunction,
                               valuet &gamma_decvar,
                               const varst &read_only_vars) const
{
#ifdef DEBUG
  std::cout << "[ACDL-DOMAIN] is_complete? "
            << from_expr(SSA.ns, "", conjunction(value))
            << std::endl;
#endif
#ifdef DEBUG
  std::cout << "The list of all variables are " << std::endl;
  for(acdl_domaint::varst::const_iterator i=symbols.begin();i!=symbols.end(); ++i)
    std::cout << from_expr(SSA.ns, "", *i) << std::endl;
#endif

  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  *solver << conjunction(value);

  // [TODO] remove "guard#" variables from ngc
  // check gamma_decvar is empty
  assert(gamma_decvar.size()==0);
#if 0
  // COMMENT: we cannot take the variables from the value
  //          because it might not contain all variables
  // find symbols in value
  std::set<symbol_exprt> symbols;
  find_symbols (conjunction(value), symbols);
#endif

  // copy the value
  valuet val_check=value;

  std::string str0("#lb");
  std::string str1("#phi");
  std::string name;


  // when there is atleast one potential
  // non-gamma complete variable
  if(ngc.size() > 0) {
#ifdef DEBUG
    std::cout << "The list of non-gamma-complete variables are " << std::endl;
    for(acdl_domaint::varst::const_iterator j=ngc.begin();j!=ngc.end(); ++j)
      std::cout << from_expr(SSA.ns, "", *j) << std::endl;
#endif
    for(std::set<symbol_exprt>::const_iterator it=symbols.begin();
        it!=symbols.end(); ++it)
    {
      // ignore the symbols whose name is of
      // type "lb", for example guard#lb3
      // Ignoring such variables does not
      // affect completeness if guard#ls=false
      // Remember, for real counterexample guard#ls has to be FALSE
      const irep_idt &identifier=it->get(ID_identifier);
      name=id2string(identifier);
      std::size_t found0=name.find(str0);
      std::size_t found1=name.find(str1);

      if (found0!=std::string::npos || found1!=std::string::npos)
        continue;
      // ignore checking of non-gamma-complete symbols
      acdl_domaint::varst::const_iterator i_op;
      i_op=find(ngc.begin(), ngc.end(), *it);
#ifdef DEBUG
      std::cout << "Comparing " << from_expr(*it) << "with ";
      for(acdl_domaint::varst::const_iterator it1=ngc.begin();it1!=ngc.end(); ++it1) {
        std::cout << from_expr(SSA.ns, "", *it1) << ", ";
        std::cout << std::endl;
      }
#endif
      if(i_op!=ngc.end()) {
        std::cout << "Ignoring non-gamma complete variable: " << from_expr(*i_op) << std::endl;
        continue;
      }
      if(read_only_vars.size() > 0) {
#ifdef DEBUG
        std::cout << "Printing read-only variables" << std::endl;
        for(acdl_domaint::varst::const_iterator it2=read_only_vars.begin();it2!=read_only_vars.end(); ++it2)
          std::cout << from_expr(SSA.ns, "", *it2) << ", ";
        std::cout << std::endl;
#endif

        // only make decisions on read_only_variables
        acdl_domaint::varst::const_iterator r_op;
        r_op=find(read_only_vars.begin(), read_only_vars.end(), *it);
        if(r_op==read_only_vars.end()) {
          continue;
        }
      }

      decision_proceduret::resultt res=(*solver)();
      assert(res==decision_proceduret::D_SATISFIABLE);

      // decide for non-singletons that
      // are potential gamma-complete candidates
      acdl_domaint::meet_irreduciblet val;
      val=split(value, *it);

      if(!val.is_false()) {
        //unsigned iter=0;
        std::cout << "Checking gamma-completeness for " << from_expr(*it) << std::endl;
        std::cout << "The new split returns " << from_expr(val) << std::endl;

#if 0
        // Following checks whether !(x=val)
        // is satisfiable.
        solver->new_context();
#ifdef DEBUG
        std::cout << "check "
                  << from_expr(SSA.ns, "", not_exprt(val));
        << std::endl;
#endif
        // and push !(val) into the solver
        *solver << not_exprt(val);
        if((*solver)()!=decision_proceduret::D_UNSATISFIABLE)
        {
          // #ifdef DEBUG
          std::cout << "is not complete since the negation of " << from_expr(*it) <<
            " is SAT " << std::endl;
          // #endif
          return false;
        }
        solver->pop_context();
#endif

        // randomly decide for non-singletons
        // [TODO] Check if "phi" variables can be
        // avoided from making decisions
        if(val.id()!=ID_le && val.id()!=ID_ge)
        {
          continue;
        }
        assert(val.id()!=ID_not);
        // convert x<=10 to x==10
        const exprt &lhs=to_binary_relation_expr(val).lhs();
        const exprt &rhs=to_binary_relation_expr(val).rhs();
        std::cout << "lhs is " << from_expr(lhs) << std::endl;
        std::cout << "rhs is " << from_expr(rhs) << std::endl;
        // exprt new_exp=binary_relation_exprt(lhs, ID_equal, rhs);
        exprt new_exp=equal_exprt(lhs, rhs);
        std::cout << "The new decision is " << from_expr(new_exp) << std::endl;
        // insert new decision to the temporary value
        val_check.push_back(new_exp);
        // assign the decision
        gamma_decvar.push_back(new_exp);
      }
      else continue;
    } // end for all symbols

    // At this point, all potential gamma-complete
    // variables have singletons values
    // check if these decisions leads to UNSAFE
    std::cout << "Decisions made in gamma-complete phase are " << std::endl;
    for(acdl_domaint::valuet::iterator g=gamma_decvar.begin();g!=gamma_decvar.end(); ++g)
      std::cout << from_expr(SSA.ns, "", *g) << ", ";
    std::cout << std::endl;
    return(gamma_complete_deduction(ssa_conjunction, val_check));
  } // case for at least one non-gamma-complete variable
  // Old gamma-completeness check
  else {
#ifdef DEBUG
    std::cout << "Normal gamma-complete check" << std::endl;
#endif
    for(std::set<symbol_exprt>::const_iterator it=symbols.begin();
        it!=symbols.end(); ++it)
    {
      // ignore the symbols whose name is of
      // type "lb", for example guard#lb3
      // Ignoring such variables does not
      // affect completeness if guard#ls=false
      // Remember, for real counterexample guard#ls has to be FALSE
      const irep_idt &identifier=it->get(ID_identifier);
      name=id2string(identifier);
      std::size_t found0=name.find(str0);
      if (found0!=std::string::npos)
        continue;

      decision_proceduret::resultt res=(*solver)();
      assert(res==decision_proceduret::D_SATISFIABLE);
      // if value==(x=[2, 2]) and (*it is x), then 'm' below contains the
      // value of x which is 2
      exprt m=(*solver).get(*it);
#ifdef DEBUG
      std::cout << "The value " << from_expr(SSA.ns, "", m) << std::endl;
#endif
      if(m.id()!=ID_constant) {
#ifdef DEBUG
        std::cout << " is not complete" << std::endl;
#endif
        return false;
      }
      solver->new_context();

#ifdef DEBUG
      std::cout << "  check "
                << from_expr(SSA.ns, "", not_exprt(equal_exprt(*it, m)))
                << std::endl;
#endif

      // and push !(x=m) into the solver
      *solver << not_exprt(equal_exprt(*it, m));

      if((*solver)()!=decision_proceduret::D_UNSATISFIABLE)
      {
#ifdef DEBUG
        std::cout << " is not complete" << std::endl;
#endif
        return false;
      }
      solver->pop_context();
    }
#ifdef DEBUG
    std::cout << " is complete" << std::endl;
#endif
    return true;
  } // normal case
}

/*******************************************************************

 Function: acdl_solvert::preprocess_val()

 Inputs:

 Outputs:

 Purpose: Pre-process abstract value to remove (x==N) constraints 
          by (x<=N) and (x>=N). The trail is not effected by this. 

\*******************************************************************/
void acdl_domaint::preprocess_val(valuet& val)
{
  valuet val_temp;
  std::vector<exprt> save_exp;
  //for(valuet::iterator it=val.begin();it!=val.end(); ++it)
  for(exprt it : val)
  {
    exprt m=it;
    if(it.id()==ID_equal)
    {
      save_exp.push_back(m);
#ifdef DEBUG
      std::cout << "Preprocessing value " << from_expr(m) << std::endl;
#endif
      exprt &lhs=to_binary_relation_expr(m).lhs();
      exprt &rhs=to_binary_relation_expr(m).rhs();
      // construct x<=N
      exprt expl=binary_relation_exprt(lhs, ID_le, rhs);
      // construct x>=N
      exprt expg=binary_relation_exprt(lhs, ID_ge, rhs);
      // [TODO] erasing causes problem 
      // val.erase(it);
      // val.insert(it, true_exprt());
      val_temp.push_back(expl);
      val_temp.push_back(expg);
#ifdef DEBUG
      std::cout << "Preprocessing inserted value " << from_expr(expl) << std::endl;
      std::cout << "Preprocessing inserted value " << from_expr(expg) << std::endl;
#endif
    }
    else {
#ifdef DEBUG
      std::cout << "Donot Preprocess value " << from_expr(m) << std::endl;
#endif
      continue;
    }
  }
 
  // [TODO] handle if there are multiple equality constraints in val
  for(std::vector<exprt>::iterator it=save_exp.begin(); it!=save_exp.end(); it++)
    val.erase(std::remove(val.begin(), val.end(), *it), val.end());
    //val.erase(std::remove(val.begin(), val.end(), save_exp), val.end());
#ifdef DEBUG
  std::cout << "Now push all collected constraints" << std::endl;
#endif
  if(val_temp.size() > 0) 
    val.insert(val.end(), val_temp.begin(), val_temp.end());
}

/*******************************************************************\

  Function: acdl_domaint::gamma_complete_deduction()

  Inputs:

  Outputs:

  Purpose: gamma-completeness deduction

\*******************************************************************/

bool acdl_domaint::gamma_complete_deduction(const exprt &ssa_conjunction,
                                            const valuet &value) const
{

  if(ssa_conjunction.id()==ID_and)
  {
    forall_operands(it, ssa_conjunction) {
      statementt statement=*it;
      std::cout << "SSA Statements: " << from_expr(*it) << std::endl;
    }
  }

  std::cout << "The abstract value is " << from_expr(conjunction(value)) << std::endl;

  std::unique_ptr<incremental_solvert> solver(
    incremental_solvert::allocate(SSA.ns, true));
  *solver << and_exprt(ssa_conjunction, conjunction(value));
  if((*solver)()==decision_proceduret::D_SATISFIABLE)
  {
    std::cout << "is complete " << std::endl;
    return true;
  }
  else {
    std::cout << "is not complete" << std::endl;
    return false;
  }

  // Note that before declaring true or false,
  // we must do two things. We must normalize
  // the value (with equality ID_equal) since
  // some variables are made equal. We must also
  // do the check that !(x=val) holds for all variables.

#if 0
  // Following checks whether !(x=val)
  // is satisfiable.
  solver->new_context();
#ifdef DEBUG
  std::cout << "check "
            << from_expr(SSA.ns, "", not_exprt(val));
  << std::endl;
#endif
  // and push !(val) into the solver
  *solver << not_exprt(val);
  if((*solver)()!=decision_proceduret::D_UNSATISFIABLE)
  {
    // #ifdef DEBUG
    std::cout << "is not complete since the negation of " << from_expr(*it) <<
      " is SAT " << std::endl;
    // #endif
    return false;
  }
  solver->pop_context();
#endif
}

/*******************************************************************\

Function: acdl_domaint::operator()

 Inputs:

 Outputs:

 Purpose: operator()

\*******************************************************************/

void acdl_domaint::operator()(
  const statementt &statement,
  const varst &vars,
  const valuet &init_value,
  const valuet &final_value,
  valuet &generalized_value)
{
  // assert(false);
}
