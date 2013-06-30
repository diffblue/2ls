/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "function_ssa.h"
#include "solver.h"

class ssa_data_flowt
{
public:
  ssa_data_flowt(const function_SSAt &_function_SSA):
    function_SSA(_function_SSA)
  {
    fixed_point();
  }

  void print_invariant(std::ostream &) const;
  
  unsigned iteration_number;

protected:
  const function_SSAt &function_SSA;
  typedef function_SSAt::locationt locationt;
  
  void fixed_point();
  bool iteration();
  void initialize_invariant();

  struct backwards_edget
  {
    locationt loc;
    solvert::var_sett in_vars, out_vars;
    solvert::predicatet predicate;
  };
  
  backwards_edget backwards_edge(locationt loc);
  
  typedef std::vector<backwards_edget> backwards_edgest;
  backwards_edgest backwards_edges;
  void get_backwards_edges();
};

