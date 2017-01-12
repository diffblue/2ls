/*******************************************************************\

Module: ACDL Decision Heuristics (range)

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/
#include <limits.h>
#include <fstream>
#include <cstdlib>
#include "acdl_solver.h"
#include "acdl_decision_heuristics_largest_range.h"

#define DEBUG 1

/*******************************************************************

 Function: acdl_solvert::operator()

 Inputs:

 Outputs:

 Purpose: Implementation of operator

\*******************************************************************/
acdl_domaint::meet_irreduciblet acdl_decision_heuristics_ranget::operator()
  (const local_SSAt &SSA, const acdl_domaint::valuet &value)
{
#ifdef DEBUG
  std::cout << "Printing all decision variables" << std::endl;
  for(std::set<exprt>::const_iterator
        it=decision_variables.begin(); it!=decision_variables.end(); it++)
    std::cout << from_expr(SSA.ns, "", *it) << "  , " << std::endl;
  std::cout << "Printing initial values of decision variables" << std::endl;
  for(std::vector<std::pair<mp_integer, mp_integer> >::iterator i=decvar_val.begin();
      i!=decvar_val.end();i++)
    std::cout << "lower " << i->first << "upper" << i->second << std::endl;
#endif

  bool decision=false;
  std::string strc("cond");
  exprt val;
  std::string name;
  std::vector<exprt> conds;
  std::vector<exprt> non_cond;
  std::set<symbol_exprt> non_cond_sym;


  // copy the value to non-constant value
  acdl_domaint::valuet v;
  for(int k=0;k<value.size();k++)
    v.push_back(value[k]);

  // copy the decision_variables in separate vector
  for(std::set<exprt>::const_iterator
        it=decision_variables.begin(); it!=decision_variables.end(); ++it)
  {
    const irep_idt &identifier=it->get(ID_identifier);
    name=id2string(identifier);
    std::size_t found=name.find(strc);
    if(found!=std::string::npos)
      conds.push_back(*it);
    else {
      non_cond.push_back(*it);
      acdl_domaint::varst sym;
      find_symbols(*it, sym);
      non_cond_sym.insert(sym.begin(), sym.end());
    }
  }

  // 1> pick a cond variable
  // 2> check if it is singleton
  // 3> If not singleton, return it.
  bool cond=false;
  for(int i=0;i<conds.size();i++) {
    const acdl_domaint::meet_irreduciblet
      exp=conds[i];
    val=domain.split(value, exp);
    if(!val.is_false()) {
      cond=true;
      return val;
    }
  }

  // cond set must be exhausted
  assert(cond==false);

  // find variable with largest
  // range relative to initial range
  bool relative=false;
  std::vector<double> scores;
  get_scores(value, scores, relative);

  double max_score=-1;
  int max_var=-1;
#ifdef VERBOSE
  std::cout << "scores: ";
#endif
  for(unsigned i=0; i<scores.size(); i++)
  {
#ifdef VERBOSE
    std::cout << scores[i] << " ";
#endif
    if(scores[i] >= 0 && scores[i] >= max_score)
    {
      max_score=scores[i];
      max_var=i;
    }
  }
#ifdef VERBOSE
  std::cout << std::endl;
#endif

  if(max_var==-1) {
    std::cout << "NO DECISIONS CAN BE MADE " << std::endl;
    return false_exprt();
  }

  int index=max_var;
  const exprt dec_var=*std::next(decision_variables.begin(), index);
  // we call split now to
  // return the decision
  val=domain.split(value, dec_var);

  // Alternatively, we can split the
  // val_pair into half and create a
  // meet irreducible with lower or upper half
  /*std::pair<mp_integer, mp_integer> current_valpair;
    current_valpair=domain.get_var_bound(value, dec_var);*/

  return val;
}

/*******************************************************************

 Function: acdl_decision_heuristics_ranget::get_score()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void acdl_decision_heuristics_ranget::get_scores(const acdl_domaint::valuet &value,
                                                 std::vector<double>& scores, bool relative)
{
  std::string name;
  std::string str("cond");
  std::vector<std::pair<mp_integer, mp_integer> >::iterator iter=decvar_val.begin();

  // The index of decision_variables set
  // and the decvar_val vector
  // are the same -- that is an entry in
  // decvar_val corresponds to the intial
  // value of the corresponding decision
  // variable at that index in decision_variables set
  for(std::set<exprt>::const_iterator
        it=decision_variables.begin(); it!=decision_variables.end(); ++it)
  {
    const irep_idt &identifier=it->get(ID_identifier);
    name=id2string(identifier);
    std::size_t found=name.find(str);
    if(found!=std::string::npos) {
      scores.push_back(-1);
      iter++;
      continue;
    }
    // largest range is computed
    // among non-cond variables
    else {
      exprt val=domain.split(value, *it);
#ifdef DEFINE
      std::cout << "Calculating score for variable " << *it << "with value" << val << std::endl;
#endif
      if(val.is_false()) {
        scores.push_back(-1);
        if(iter!=decvar_val.end())
          iter++;
        continue;
      }

      // find the non-cond variable
      // with the largest range
#ifdef DEFINE
      std::cout << "Calculating scores for variable " << *it << std::endl;
#endif
      std::pair<mp_integer, mp_integer> current_valpair, initial_valpair;
      current_valpair=domain.get_var_bound(value, *it);
      initial_valpair=*iter;
      if(iter!=decvar_val.end())
        iter++;

      if(relative)
        scores.push_back(get_ratio(current_valpair, initial_valpair));
      else
        scores.push_back(get_ratio(current_valpair, initial_valpair));
    }
  }
}

/*******************************************************************

 Function: acdl_decision_heuristics_ranget::get_ratio()

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

double acdl_decision_heuristics_ranget::get_ratio
(std::pair<mp_integer, mp_integer> i1, std::pair<mp_integer, mp_integer> i2)
{
  mp_integer r1=i1.second-i1.first;
  mp_integer r2=i2.second-i2.first;
#ifdef DEFINE
  std::cout << "Calculating ratio for " << r1 << ", " << r2 << std::endl;
#endif
  unsigned long ur2;
  if(!r2.is_ulong())
    ur2=ULONG_MAX;
  else
    ur2=r2.to_ulong();

  unsigned long ur1;
  if(!r1.is_ulong())
    ur1=ULONG_MAX;
  else
    ur1=r1.to_ulong();

  double result=double(ur1)/ur2;
#ifdef DEFINE
  std::cout << "ratio " << ur1 << "/" << ur2 << "Result" << result << std::endl;
#endif
  assert(result >= 0 && result<=1);
  return result;
}
