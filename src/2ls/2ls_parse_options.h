/*******************************************************************\

Module: 2LS Command Line Parsing

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// 2LS Command Line Parsing

#ifndef CPROVER_2LS_2LS_2LS_PARSE_OPTIONS_H
#define CPROVER_2LS_2LS_2LS_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>
#include <util/replace_symbol.h>

#include <goto-programs/goto_check.h>
#include <ssa/dynamic_objects.h>

class goto_modelt;
class optionst;

#include "summary_checker_base.h"

// clang-format off
#define TWOLS_OPTIONS \
  "(xml-ui)" \
  "(function):" \
  "D:I:" \
  "(depth):(context-bound):(unwind):" \
  OPT_GOTO_CHECK \
  "(non-incremental)" \
  "(no-assertions)(no-assumptions)" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(object-bits):" \
  "(little-endian)(big-endian)" \
  "(error-label):(verbosity):(no-library)" \
  "(version)" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)(gcc)" \
  "(ppc-macos)(unsigned-char)" \
  "(havoc)" \
  "(intervals)" \
  "(zones)" \
  "(octagons)" \
  "(equalities)" \
  "(heap)" \
  "(values-refine)" \
  "(sympath)" \
  "(enum-solver)(binsearch-solver)(arrays)"\
  "(string-abstraction)(no-arch)(arch):(floatbv)(fixedbv)" \
  "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)" \
  "(inline)(inline-main)(inline-partial):(instrument-output):" \
  "(context-sensitive)(termination)(nontermination)" \
  "(lexicographic-ranking-function):(monolithic-ranking-function)" \
  "(max-inner-ranking-iterations):" \
  "(preconditions)(sufficient)" \
  "(show-locs)(show-vcc)(show-properties)(trace)(show-stats)" \
  "(show-goto-functions)(show-guards)(show-defs)(show-ssa)(show-assignments)" \
  "(show-invariants)(std-invariants)" \
  "(show-symbol-table)" \
  "(property):(all-properties)(k-induction)(incremental-bmc)" \
  "(no-spurious-check)(all-functions)" \
  "(no-simplify)(no-fixed-point)" \
  "(graphml-witness):(json-cex):" \
  "(no-spurious-check)(stop-on-fail)" \
  "(competition-mode)(slice)(no-propagation)(independent-properties)" \
  "(no-unwinding-assertions)"
  // the last line is for CBMC-regression testing only
// clang-format on

class twols_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit();
  virtual void help();

  twols_parse_optionst(int argc, const char **argv);

protected:
  goto_modelt goto_model;
  ui_message_handlert ui_message_handler;
  bool recursion_detected;
  bool threads_detected;
  std::unique_ptr<dynamic_objectst> dynamic_objects;

  virtual void register_languages();

  void get_command_line_options(optionst &options);

  bool get_goto_program(const optionst &options);

  bool process_goto_program(
    const optionst &options,
    goto_modelt &goto_model);

  bool set_properties(goto_modelt &);

  void report_success();
  void report_failure();

  void report_properties(
    const optionst &options,
    const goto_modelt &,
    const propertiest &,
    const tracest &traces);

  void show_counterexample(
    const goto_modelt &,
    const class goto_tracet &);

  void output_graphml_cex(
    const optionst &options,
    const goto_modelt &,
    const summary_checker_baset &summary_checker);

  void output_graphml_proof(
    const optionst &options,
    const goto_modelt &goto_model,
    const summary_checker_baset &summary_checker);

  void output_json_cex(
    const optionst &options,
    const goto_modelt &goto_model,
    const goto_tracet &error_trace,
    const std::string &property_id);

  struct expr_statst
  {
    bool has_malloc;
    bool has_string;
    bool has_array;
    bool has_pointer;

    expr_statst():
      has_malloc(false),
      has_string(false),
      has_array(false),
      has_pointer(false)
    {
    }
  };

  void type_stats_rec(
    const typet &type,
    expr_statst &stats,
    const namespacet &ns);

  void expr_stats_rec(
    const exprt &expr,
    expr_statst &stats);

  void show_stats(
    const goto_modelt &,
    std::ostream &);

  void eval_verbosity();
  void report_unknown();

  bool has_threads(const goto_modelt &goto_model);

  // diverse preprocessing
  void inline_main(goto_modelt &goto_model);
  void propagate_constants(goto_modelt &goto_model);
  void nondet_locals(goto_modelt &goto_model);
  bool unwind_goto_into_loop(goto_modelt &goto_model, unsigned k);
  void remove_multiple_dereferences(goto_modelt &goto_model);
  void remove_multiple_dereferences(
    goto_modelt &goto_model,
    goto_programt &body,
    goto_programt::targett t,
    exprt &expr,
    unsigned &var_counter,
    bool deref_seen);
  void add_assumptions_after_assertions(goto_modelt &goto_model);
  void filter_assertions(goto_modelt &goto_model);
  void split_loopheads(goto_modelt &goto_model);
  void remove_loops_in_entry(goto_modelt &goto_model);
  void create_dynamic_objects(goto_modelt &goto_model);
  void add_dynamic_object_rec(exprt &expr, symbol_tablet &symbol_table);
  void split_same_symbolic_object_assignments(goto_modelt &goto_model);
  void remove_dead_goto(goto_modelt &goto_model);
  void memory_assert_info(goto_modelt &goto_model);
  void handle_freed_ptr_compare(goto_modelt &goto_model);
  void assert_no_unsupported_functions(goto_modelt &goto_model);
  void assert_no_atexit(goto_modelt &goto_model);
  void fix_goto_targets(goto_modelt &goto_model);
  void make_assertions_false(goto_modelt &goto_model);
  void make_symbolic_array_indices(goto_modelt &goto_model);
  void make_scanf_nondet(goto_modelt &goto_model);
};

#endif
