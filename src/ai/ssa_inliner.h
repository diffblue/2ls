/*******************************************************************\

Module: SSA Inliner

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_SSA_INLINER_H
#define CPROVER_DELTACHECK_SSA_INLINER_H

#include "summary.h"
#include "../ssa/local_ssa.h"

class ssa_inlinert
{
 public:
  ssa_inlinert() : counter(0) {}

  void replace(local_SSAt::nodest &nodes,
	       local_SSAt::nodest::iterator node,
               local_SSAt::nodet::equalitiest::iterator equ_it, 
	       const local_SSAt::var_sett &globals, //names of globals at call site
               const summaryt &summary);

  //TODO: problem: local_SSAt::nodest maps a goto program target to a single SSA node,
  //               for inlining we require a target to map to several SSA nodes
  void replace(local_SSAt::nodest &nodes,
	       local_SSAt::nodest::iterator node, 
               local_SSAt::nodet::equalitiest::iterator equ_it, 
	       const local_SSAt::var_sett &globals, //names of globals at call site
               const local_SSAt &function);

  void havoc(local_SSAt::nodet &node, 
	     local_SSAt::nodet::equalitiest::iterator &equ_it);

  //apply changes to node, must be called after replace and havoc
  void commit_node(local_SSAt::nodest::iterator node);
  void commit_nodes(local_SSAt::nodest &nodes);

 protected:
  unsigned counter;
  local_SSAt::nodest new_nodes;
  local_SSAt::nodet::equalitiest new_equs;
  std::set<local_SSAt::nodet::equalitiest::iterator> rm_equs;

 private:
  void replace_globals_in(const local_SSAt::var_sett &globals_in, 
                          const local_SSAt::var_sett &globals);
  void replace_params(const local_SSAt::var_listt &params,
                      const function_application_exprt &funapp_expr);
  void replace_return_values(local_SSAt::nodest::iterator node, 
			     local_SSAt::nodet::equalitiest::iterator equ_it,
			     const local_SSAt::var_sett &returns);
  void replace_globals_out(local_SSAt::nodest &nodes,
			   local_SSAt::nodest::iterator node,
			   const local_SSAt::var_sett &globals_out);

  void rename(exprt &expr);
  void rename_globals(exprt &expr, const local_SSAt::var_sett &globals);

  bool find_corresponding_symbol(const symbol_exprt &s, 
				 const local_SSAt::var_sett &globals,
                                 symbol_exprt &s_found);

  irep_idt get_original_identifier(const symbol_exprt &s);

};


#endif
