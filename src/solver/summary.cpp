/*******************************************************************\

Module: Summary

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Summary

#ifdef DEBUG
#include <langapi/language_util.h>
#endif

#include <domains/util.h>

#include "summary.h"

// #define PRETTY_PRINT

void summaryt::output(std::ostream &out, const namespacet &ns) const
{
  out << "params: ";
  for(summaryt::var_listt::const_iterator it=params.begin();
      it!=params.end(); it++)
    out << from_expr(ns, "", *it) << " ";
  out << std::endl;
  out << "globals_in: ";
  for(summaryt::var_sett::const_iterator it=globals_in.begin();
      it!=globals_in.end(); it++)
    out << from_expr(ns, "", *it) << " ";
  out << std::endl;
  out << "globals_out: ";
  for(summaryt::var_sett::const_iterator it=globals_out.begin();
      it!=globals_out.end(); it++)
    out << from_expr(ns, "", *it) << " ";
  out << std::endl;
  out << "forward precondition: "
      << (fw_precondition.is_nil() ? "not computed" :
    from_expr(ns, "", fw_precondition)) << std::endl;
  out << "forward transformer: "
      << (fw_transformer.is_nil() ? "not computed" :
    from_expr(ns, "", fw_transformer)) << std::endl;
  out << "forward invariant: "
      << (fw_invariant.is_nil() ? "not computed" :
    from_expr(ns, "", fw_invariant)) << std::endl;
  out << "backward precondition: "
      << (bw_precondition.is_nil() ? "not computed" :
    from_expr(ns, "", bw_precondition)) << std::endl;
  out << "backward postcondition: "
      << (bw_postcondition.is_nil() ? "not computed" :
    from_expr(ns, "", bw_postcondition)) << std::endl;
  out << "backward transformer: "
      << (bw_transformer.is_nil() ? "not computed" :
    from_expr(ns, "", bw_transformer)) << std::endl;
  out << "backward invariant: "
      << (bw_invariant.is_nil() ? "not computed" :
    from_expr(ns, "", bw_invariant)) << std::endl;
  out << "termination argument: ";
  if(termination_argument.is_nil())
    out << "not computed";
  else
#if PRETTY_PRINT
    pretty_print_termination_argument(out, ns, termination_argument);
#else
    out << from_expr(ns, "", termination_argument) << std::endl;
#endif
  out << std::endl;
  out << "terminates: " << threeval2string(terminates) << std::endl;
}

void summaryt::combine_and(exprt &olde, const exprt &newe)
{
  if(olde.is_nil())
  {
    olde=newe;
  }
  else
  {
    if(newe.is_nil())
      return;

    olde=and_exprt(olde, newe);
  }
}

void summaryt::combine_or(exprt &olde, const exprt &newe)
{
  if(olde.is_nil())
  {
    olde=newe;
  }
  else
  {
    if(newe.is_nil())
      return;
    olde=or_exprt(olde, newe);
  }
}

void summaryt::join(const summaryt &new_summary)
{
  assert(params==new_summary.params);
  assert(globals_in==new_summary.globals_in);
  assert(globals_out==new_summary.globals_out);
  combine_or(fw_precondition, new_summary.fw_precondition);
  combine_and(fw_transformer, new_summary.fw_transformer);
  combine_and(fw_invariant, new_summary.fw_invariant);
  combine_and(bw_precondition, new_summary.bw_precondition);
  combine_or(bw_postcondition, new_summary.bw_postcondition);
  combine_and(bw_transformer, new_summary.bw_transformer);
  combine_and(bw_invariant, new_summary.bw_invariant);
  combine_and(termination_argument, new_summary.termination_argument);
  switch(new_summary.terminates)
  {
  case YES:
    break;
  case NO: terminates=NO;
    break;
  case UNKNOWN:
    if(terminates!=NO)
      terminates=UNKNOWN;
    break;
  default: assert(false);
  }
}

/// Get value domain for last location from SSA.
void summaryt::set_value_domains(const local_SSAt &SSA)
{
  const local_SSAt::locationt &entry_loc=SSA.nodes.begin()->location;
  const local_SSAt::locationt &exit_loc=(--SSA.nodes.end())->location;
  value_domain_in=SSA.ssa_value_ai[entry_loc];
  value_domain_out=SSA.ssa_value_ai[exit_loc];
}

std::string threeval2string(threevalt v)
{
  switch(v)
  {
  case YES: return "yes";
  case NO: return "no";
  case UNKNOWN: return "unknown";
  }
  assert(false);
}
