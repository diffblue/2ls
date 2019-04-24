/*******************************************************************\

Module: SSA

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// SSA

#ifndef CPROVER_2LS_SSA_LOCAL_SSA_H
#define CPROVER_2LS_SSA_LOCAL_SSA_H

#include <util/std_expr.h>

#include <goto-programs/goto_functions.h>

#include <domains/list_iterator.h>
#include <domains/incremental_solver.h>

#include "ssa_domain.h"
#include "guard_map.h"
#include "ssa_object.h"
#include "ssa_heap_domain.h"
#include "may_alias_analysis.h"

#define TEMPLATE_PREFIX "__CPROVER_template"
#define TEMPLATE_DECL TEMPLATE_PREFIX
#define TEMPLATE_NEWVAR TEMPLATE_PREFIX "_newvar"
#define TEMPLATE_PARAM_PREFIX TEMPLATE_PREFIX "_param"

class local_SSAt
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;
  typedef goto_programt::const_targett locationt;

  inline local_SSAt(
    const goto_functiont &_goto_function,
    const namespacet &_ns,
    const ssa_heap_analysist &_heap_analysis,
    const std::string &_suffix=""):
    ns(_ns), goto_function(_goto_function),
    heap_analysis(_heap_analysis),
    ssa_objects(_goto_function, ns, _heap_analysis),
    ssa_value_ai(_goto_function, ns, _heap_analysis),
    assignments(
      _goto_function.body, ns, ssa_objects, ssa_value_ai, heap_analysis),
    alias_analysis(_goto_function, ns),
    guard_map(_goto_function.body),
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

    typedef std::vector<function_application_exprt> function_callst;
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

  std::set<list_iteratort> iterators;

  // unknown heap objects
  var_sett unknown_objs;

  // Maps members of dynamic object to a set of pointers used to access those
  // objects when assigning them
  class dyn_obj_assignt
  {
  public:
    const irep_idt pointer_id;
    const exprt cond;

    dyn_obj_assignt(const irep_idt &pointer_id, const exprt &cond):
      pointer_id(pointer_id), cond(cond) {}
  };
  typedef std::list<dyn_obj_assignt> dyn_obj_assignst;
  std::map<exprt, dyn_obj_assignst> dyn_obj_assigns;

  // Map dynamic object names to guards of their allocation
  std::map<irep_idt, exprt> allocation_guards;

  bool has_function_calls() const;

  const namespacet &ns;
  const goto_functiont &goto_function;

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

  void collect_iterators_rhs(const exprt &expr, locationt loc);
  void collect_iterators_lhs(const ssa_objectt &object, locationt loc);
  void new_iterator_access(
    const member_exprt &expr,
    locationt loc,
    unsigned inst_loc_number);

  exprt unknown_obj_eq(
    const symbol_exprt &obj,
    const struct_typet::componentt &component) const;

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

  const ssa_heap_analysist &heap_analysis;

  ssa_objectst ssa_objects;
  typedef ssa_objectst::objectst objectst;
  ssa_value_ait ssa_value_ai;
  assignmentst assignments;

  may_alias_analysist alias_analysis;

// protected:
  guard_mapt guard_map;

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
  void build_assertions(locationt loc);
  void build_unknown_objs(locationt loc);

  void collect_allocation_guards(const code_assignt &assign, locationt loc);
  void get_alloc_guard_rec(const exprt &expr, exprt old_guard);
  void collect_record_frees(locationt loc);

  // custom templates
  void collect_custom_templates();
  replace_mapt template_newvars;
  exprt template_last_newvar;
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
