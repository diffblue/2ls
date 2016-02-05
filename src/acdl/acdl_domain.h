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

  //TODO: need to return information about inferred meet irreducibles
  //        and which meet irreducibles were used to infer this information
  void operator()(const statementt &statement,
		  const varst &vars,
		  const valuet &old_value,
		  valuet &new_value,
		  deductionst &deductions);

  void meet(const std::vector<valuet> &old_values,
	    valuet &new_value);
  void meet(const valuet &old_value, valuet &new_value);
  void meet(const meet_irreduciblet &old_value, valuet &new_value);

  void join(const std::vector<valuet> &old_values,
	    valuet &new_value);
    
  bool contains(const valuet &value1,
		const valuet &value2) const;

  meet_irreduciblet split(const valuet &value, const exprt &expr, bool upper=false);
  
  void normalize(valuet &value, const varst &vars);

  void set_bottom(valuet &value) { value.clear(); value.push_back(false_exprt());  }
  void set_top(valuet &value) { value.clear(); }

  bool is_bottom(const valuet &value) const;
  bool is_top(const valuet &value) const { return value.empty(); }
  bool is_complete(const valuet &value, const varst& vars) const;


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
  
protected:
  optionst &options;
  local_SSAt &SSA;
  ssa_dbt &ssa_db;
  ssa_local_unwindert &ssa_local_unwinder;

  exprt remove_var(const valuet &_old_value, 
    const symbol_exprt &var);
  
};

/*
class meet_irreducible : public acdl_domaint
{
public: 
 meet_irreducible(const acdl_domaint::valuet& val)
     :acdl_domaint(val)
 {
   //must be complementable
   assert(is_bottom(val) || is_meet_irreducible(val));
 }

 meet_irreducible complement() const;
}
*/

#endif
 
