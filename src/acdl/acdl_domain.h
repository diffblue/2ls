/*******************************************************************\

Module: Abstract Domain Interface for ACDL

Author: Daniel Kroening, kroening@kroening.com

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
		const valuet &value2);

  exprt remove_var(const valuet &_old_value, 
    const varst &vars);


  void set_bot() { __bot = true;  }
  void set_top() { __bot = false; }

  bool is_bot() const { return __bot; }
  bool is_empty() const;
  bool is_top() const { return !__bot; }
  bool is_complete(const exprt &expr)
  {
    if(expr.id() == ID_constant)
      return true;
    else
      return false;
  }

protected:
  optionst &options;
  local_SSAt &SSA;
  ssa_dbt &ssa_db;
  ssa_local_unwindert &ssa_local_unwinder;
  bool __bot;
  
};


#endif
 
