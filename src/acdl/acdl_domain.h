/*******************************************************************\

Module: Abstract Domain Interface for ACDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ACDL_DOMAIN_H
#define CPROVER_ACDL_DOMAIN_H

#include "../ssa/local_ssa.h"

class acdl_domaint : public messaget
{
public:
  typedef exprt valuet;
  typedef exprt statementt;
  typedef std::vector<symbol_exprt> varst;

  explicit acdl_domaint(local_SSAt &_SSA,
			ssa_dbt &_ssa_db,
			ssa_local_unwindert &_ssa_local_unwinder)
    : SSA(_SSA), ssa_db(_ssa_db), ssa_local_unwinder(_ssa_local_unwinder)
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
    
  bool contains(const valuet &new_value,
		const valuet &old_value);

protected:
  local_SSAt &SSA;
  ssa_dbt &ssa_db;
  ssa_local_unwindert &_ssa_localunwinder;
  
};


#endif
 
