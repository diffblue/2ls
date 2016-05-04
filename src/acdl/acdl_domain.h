/*******************************************************************\

Module: Abstract Domain Interface for ACDL

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ACDL_DOMAIN_H
#define CPROVER_ACDL_DOMAIN_H

#include "../ssa/local_ssa.h"
#include "../ssa/ssa_unwinder.h"
#include "../summarizer/ssa_db.h"

class acdl_domaint : public messaget
{
public:
  typedef exprt meet_irreduciblet;
  typedef std::vector<meet_irreduciblet> valuet; 
  typedef std::vector<meet_irreduciblet> antecedentst;
  typedef std::pair<meet_irreduciblet, antecedentst> deductiont;
  typedef std::vector<deductiont> deductionst;
  typedef exprt statementt;
  typedef std::set<symbol_exprt> varst;

  explicit acdl_domaint(optionst &_options,
			local_SSAt &_SSA,
			ssa_dbt &_ssa_db,
			ssa_local_unwindert &_ssa_local_unwinder)
    : options(_options), SSA(_SSA), ssa_db(_ssa_db),
      ssa_local_unwinder(_ssa_local_unwinder)
    {
      SSA.mark_nodes();
    }  

  void operator()(const statementt &statement,
		  const varst &vars,
		  const valuet &old_value,
		  valuet &new_value,
		  deductionst &deductions);

  //project deductions to value
  void to_value(const deductionst &deductions, valuet& value)
  {
    for(deductionst::const_iterator it = deductions.begin();
	it != deductions.end(); ++it)
      value.push_back(it->first);
  }

  void meet(const valuet &old_value, valuet &new_value);
  void meet(const meet_irreduciblet &old_value, valuet &new_value);

  void join(const std::vector<valuet> &old_values,
	    valuet &new_value);
    
  bool is_subsumed(const meet_irreduciblet &m,
		   const valuet &value) const;
  bool is_contained(const meet_irreduciblet &m,
		   const valuet &value) const;

  void build_meet_irreducible_templates(
    const varst &vars,
    std::vector<exprt> &meet_irreducible_templates);
  meet_irreduciblet split(
    const valuet &value,
    const exprt &meet_irreducible_template,
    bool upper=false);
  
  void normalize(valuet &value);
  void normalize_val(valuet &value);
  void expr_to_value(const exprt &expr, valuet &value);
  bool check_val(const exprt &expr);

  void set_bottom(valuet &value) { value.clear(); value.push_back(false_exprt());  }
  void set_top(valuet &value) { value.clear(); }

  bool is_bottom(const valuet &value) const;
  bool is_top(const valuet &value) const { return value.empty(); }
  bool is_complete(const valuet &value, 
		   const std::set<symbol_exprt> &symbols) const;

  //print value
  inline std::ostream &output(
    std::ostream &out, const valuet &v)
  {
    for(valuet::const_iterator it = v.begin();
	it != v.end(); ++it)
    {
      if(it != v.begin())
	out << " && ";
      out << from_expr(SSA.ns, "", *it);
    }
    return out;
  }

  //print deductions
  inline std::ostream &output(
    std::ostream &out, const deductionst &d)
  {
    for(deductionst::const_iterator it = d.begin();
	it != d.end(); ++it)
    {
      out << from_expr(SSA.ns, "", it->first) << " <== ";
      output(out,it->second) << std::endl;
    }
    return out;
  }
  
protected:
  optionst &options;
  local_SSAt &SSA;
  ssa_dbt &ssa_db;
  ssa_local_unwindert &ssa_local_unwinder;

  void remove_var(const valuet &_old_value, 
		  const symbol_exprt &var,
		  valuet &new_value);
 
  void remove_expr(valuet &old_value, 
			             exprt &expr,
                   valuet &new_value);

  void get_antecedents(incremental_solvert &solver,
		       const valuet &value,
		       const bvt &value_literals,
		       antecedentst &antecedents);

  bool expr_is_true(const exprt &expr);
 
};

#endif
 
