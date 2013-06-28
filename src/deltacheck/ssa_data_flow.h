/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "function_ssa.h"

class ssa_data_flowt
{
public:
  ssa_data_flowt(const function_SSAt &_function_SSA):
    function_SSA(_function_SSA)
  {
    fixed_point();
  }

protected:
  const function_SSAt &function_SSA;
  
  void fixed_point();

};

