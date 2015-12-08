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
  typedef exprt valuet;
  typedef exprt statementt;
  typedef std::vector<symbol_exprt> varst;

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
		  valuet &new_value);

  void meet(const std::vector<valuet> &old_values,
	    valuet &new_value);

  void join(const std::vector<valuet> &old_values,
	    valuet &new_value);
    
  bool contains(const valuet &value1,
		const valuet &value2) const;

  exprt split(const valuet &value, const exprt &expr, bool upper=false);
  

  void set_bottom(valuet &value) { value = false_exprt();  }
  void set_top(valuet &value) { value = true_exprt(); }

  bool is_bottom(const valuet &value) const;
  bool is_top(const valuet &value) const { return value.is_true(); }
  bool is_complete(const exprt &expr) const;

protected:
  optionst &options;
  local_SSAt &SSA;
  ssa_dbt &ssa_db;
  ssa_local_unwindert &ssa_local_unwinder;

  exprt remove_var(const valuet &_old_value, 
    const symbol_exprt &var);
  
};


#endif
 
