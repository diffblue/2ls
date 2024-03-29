/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA

#ifndef CPROVER_2LS_SSA_LOCAL_SSA_H
#define CPROVER_2LS_SSA_LOCAL_SSA_H

#include <util/options.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include <domains/incremental_solver.h>

#include "array_index_analysis.h"
#include "guard_map.h"
#include "may_alias_analysis.h"
#include "ssa_domain.h"
#include "ssa_object.h"

#define TEMPLATE_PREFIX "__CPROVER_template"
#define TEMPLATE_DECL TEMPLATE_PREFIX
#define TEMPLATE_NEWVAR TEMPLATE_PREFIX "_newvar"
#define TEMPLATE_PARAM_PREFIX TEMPLATE_PREFIX "_param"

class dynamic_objectst;

class local_SSAt
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::const_targett locationt;

  inline local_SSAt(const irep_idt &_function_identifier,
                    const goto_functiont &_goto_function,
                    const symbol_tablet &_symbol_table,
                    dynamic_objectst &_dynamic_objects,
                    const optionst &_options,
                    const std::string &_suffix = "")
    : ns(_symbol_table),
      goto_function(_goto_function),
      options(_options),
      dynamic_objects(_dynamic_objects),
      ssa_objects(_goto_function, ns),
      ssa_value_ai(_function_identifier, _goto_function, ns, options),
      assignments(_goto_function.body,
                  ns,
                  dynamic_objects,
                  options,
                  ssa_objects,
                  ssa_value_ai),
      array_index_analysis(_function_identifier,
                           _goto_function,
                           ns,
                           ssa_value_ai),
      guard_map(_goto_function.body),
      function_identifier(_function_identifier),
      ssa_analysis(assignments),
      suffix(_suffix)
  {
    // ENHANCE: in future locst will be used (currently in path-symex/locs.h)
    forall_goto_program_instructions(it, _goto_function.body)
      location_map[it->location_number]=it;

    build_SSA();
  }

  void output(std::ostream &) const;
  virtual void output_verbose(std::ostream &) const;

  // the SSA node for a location
  class nodet
  {
  public:
    inline nodet(
      locationt _location,
      std::list<nodet>::iterator _loophead):
      enabling_expr(true_exprt()),
      marked(false),
      location(_location),
      loophead(_loophead)
    {
    }

    typedef std::vector<equal_exprt> equalitiest;
    equalitiest equalities;

    typedef std::vector<exprt> constraintst;
    constraintst constraints;

    typedef std::vector<exprt> assertionst;
    assertionst assertions;

    typedef std::vector<code_function_callt> function_callst;
    function_callst function_calls;

    exprt enabling_expr; // for incremental unwinding
    bool marked; // for incremental unwinding

    // custom invariant templates
    typedef std::vector<exprt> templatest;
    templatest templates;

    locationt location; // link to goto instruction
    std::list<nodet>::iterator loophead; // link to loop head node
       // otherwise points to nodes.end()

    exprt record_free=nil_exprt();

    void output(std::ostream &, const namespacet &) const;

    inline bool empty() const
    {
      return equalities.empty() && constraints.empty() &&
      assertions.empty() && function_calls.empty();
    }
  };

  // turns the assertions in the function into constraints
  void assertions_to_constraints();

  // all the SSA nodes
  typedef std::list<nodet> nodest;
  nodest nodes;

  void mark_nodes()
  {
    for(nodest::iterator n_it=nodes.begin();
        n_it!=nodes.end(); n_it++)
      n_it->marked=true;
  }
  void unmark_nodes()
  {
    for(nodest::iterator n_it=nodes.begin();
        n_it!=nodes.end(); n_it++)
      n_it->marked=false;
  }

  // for incremental unwinding
  std::list<symbol_exprt> enabling_exprs;
  exprt get_enabling_exprs() const;

  // function entry and exit variables
  typedef std::list<symbol_exprt> var_listt;
  typedef std::set<symbol_exprt> var_sett;
  var_listt params;
  var_sett globals_in, globals_out;

  bool has_function_calls() const;

  const namespacet ns;
  const goto_functiont &goto_function;
  const optionst &options;
  dynamic_objectst &dynamic_objects;

  // guards
  ssa_objectt cond_symbol() const;
  symbol_exprt cond_symbol(locationt loc) const
  { return name(cond_symbol(), OUT, loc); }
  ssa_objectt guard_symbol() const;
  symbol_exprt guard_symbol(locationt loc) const
  { return name(guard_symbol(), OUT, guard_map[loc].guard_source); }
  exprt edge_guard(locationt from, locationt to) const;

  // auxiliary functions
  enum kindt { PHI, OUT, LOOP_BACK, LOOP_SELECT, OBJECT_SELECT };
  virtual symbol_exprt name(
    const ssa_objectt &,
    kindt kind,
    locationt loc) const;
  symbol_exprt name(const ssa_objectt &, const ssa_domaint::deft &) const;
  symbol_exprt name_input(const ssa_objectt &) const;
  virtual exprt nondet_symbol(
    std::string prefix,
    const typet &type,
    locationt loc,
    unsigned counter) const;
  locationt get_def_loc(const symbol_exprt &, locationt loc) const;
  void replace_side_effects_rec(exprt &, locationt, unsigned &) const;
  exprt read_lhs(const exprt &, locationt loc) const;
  exprt read_rhs(const exprt &, locationt loc) const;
  exprt read_rhs_address_of_rec(const exprt &expr, locationt loc) const;
  exprt read_rhs_rec(const exprt &, locationt loc) const;
  symbol_exprt read_rhs(const ssa_objectt &, locationt loc) const;
  exprt read_node_in(const ssa_objectt &, locationt loc) const;
  void assign_rec(
    const exprt &lhs,
    const exprt &rhs,
    const exprt &guard,
    locationt loc,
    bool fresh_rhs=false);

  void get_entry_exit_vars();

  bool has_static_lifetime(const ssa_objectt &) const;
  bool has_static_lifetime(const exprt &) const;

  exprt dereference(const exprt &expr, locationt loc) const;

  bool all_symbolic_deref_defined(
    const exprt &expr,
    const namespacet &ns,
    locationt loc) const;

  exprt concretise_symbolic_deref_rhs(
    const exprt &rhs,
    const namespacet &ns,
    const locationt loc);

  bool can_reuse_symderef(
    ssa_objectt &symderef,
    const namespacet &ns,
    const locationt loc);

  exprt get_fresh_rhs(const exprt &rhs, locationt loc);

  ssa_objectst ssa_objects;
  typedef ssa_objectst::objectst objectst;
  ssa_value_ait ssa_value_ai;
  assignmentst assignments;

  array_index_analysist array_index_analysis;

  // protected:
  guard_mapt guard_map;

  const irep_idt &function_identifier;
  ssa_ait ssa_analysis;
  std::string suffix; // an extra suffix

  // Collect all loop_guards that will represent symbolic paths used in heap
  // domain
  std::set<std::pair<symbol_exprt, symbol_exprt>> loop_guards;

  void get_globals(
    locationt loc,
    std::set<symbol_exprt> &globals,
    bool rhs_value=true,
    bool with_returns=true,
    const irep_idt &returns_for_function="") const;

  nodest::iterator find_node(locationt loc);
  nodest::const_iterator find_node(locationt loc) const;
  void find_nodes(
    locationt loc,
    std::list<nodest::const_iterator> &_nodes) const;

  inline locationt get_location(unsigned location_number) const
  {
    location_mapt::const_iterator it=location_map.find(location_number);
    assert(it!=location_map.end());
    return it->second;
  }
  locationt get_loc_with_symbol_def(const symbol_exprt &symbol) const;

protected:
  typedef std::map<unsigned, locationt> location_mapt;
  location_mapt location_map;
  // build the SSA formulas
  void build_SSA();

  // incoming and outgoing data-flow
  void build_phi_nodes(locationt loc);
  void build_transfer(locationt loc);
  void build_cond(locationt loc);
  void build_guard(locationt loc);
  void build_function_call(locationt loc);
  bool get_deallocated_precondition(const exprt &expr, exprt &result);
  void build_assertions(locationt loc);

  // competition-mode specific checks
  void disable_unsupported_instructions(locationt loc);

  void collect_record_frees(locationt loc);

  // custom templates
  void collect_custom_templates();
  replace_mapt template_newvars;
  exprt template_last_newvar;

  optionalt<ssa_domaint::deft> get_recent_object_alloc_def(
    locationt loc,
    const ssa_domaint::def_mapt::const_iterator &def) const;
};

std::list<exprt> & operator <<
  (std::list<exprt> &dest, const local_SSAt &src);

void preprocess_returns(goto_functionst::goto_functiont &goto_function);
symbol_exprt return_symbol(typet type, local_SSAt::locationt loc);

class decision_proceduret & operator <<
  (class decision_proceduret &dest, const local_SSAt &src);

class incremental_solvert & operator <<
  (class incremental_solvert &dest, const local_SSAt &src);

#endif
