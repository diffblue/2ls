/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_SSA_DATA_FLOW_H
#define DELTACHECK_SSA_DATA_FLOW_H

#include <util/threeval.h>

#include "function_ssa.h"
#include "solver.h"
#include "predicate.h"
#include "properties.h"

class ssa_data_flowt
{
public:
  typedef function_SSAt::locationt locationt;

  explicit ssa_data_flowt(
    const function_SSAt &_function_SSA_old,
    const function_SSAt &_function_SSA_new,
    const namespacet &_ns):
    function_SSA_old(_function_SSA_old),
    function_SSA_new(_function_SSA_new),
    ns(_ns),
    use_old(true)
  {
    fixed_point();
  }

  explicit ssa_data_flowt(
    const function_SSAt &_function_SSA,
    const namespacet &_ns):
    function_SSA_old(_function_SSA),
    function_SSA_new(_function_SSA),
    ns(_ns),
    use_old(false)
  {
    fixed_point();
  }

  void print_invariant(std::ostream &) const;
  
  unsigned iteration_number;

  propertiest properties;
  
protected:
  const function_SSAt &function_SSA_old;
  const function_SSAt &function_SSA_new;
  const namespacet &ns;
  bool use_old;
  
  void fixed_point();
  bool iteration();
  void initialize_invariant();

  struct backwards_edget
  {
    locationt from, to;
    predicatet pre_predicate, post_predicate;
  };
  
  backwards_edget backwards_edge(
    const function_SSAt &function_SSA, locationt loc);
  
  typedef std::vector<backwards_edget> backwards_edgest;
  backwards_edgest backwards_edges;
  void get_backwards_edges();

  void check_properties();
  void setup_properties();
};

#endif
