/*******************************************************************\

Module: 2LS Command Line Options Processing

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// 2LS Command Line Options Processing

#include <memory>
#include <iostream>
#include <fstream>
#include <climits>

#include <util/string2int.h>
#include <util/config.h>
#include <util/language.h>
#include <util/options.h>
#include <util/memory_info.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_inline_class.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/xml_goto_trace.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_skip.h>

#include <analyses/goto_check.h>

#include <langapi/mode.h>

#include <cbmc/version.h>
#include "version.h"

#include <ssa/malloc_ssa.h>

#include "graphml_witness_ext.h"
#include <solver/summary_db.h>
#include <ssa/dynobj_instance_analysis.h>

#include "2ls_parse_options.h"
#include "summary_checker_ai.h"
#include "summary_checker_bmc.h"
#include "summary_checker_kind.h"
#include "summary_checker_nonterm.h"
#include "show.h"
#include "horn_encoding.h"

#define UNWIND_GOTO_INTO_LOOP 0
#define REMOVE_MULTIPLE_DEREFERENCES 1
#define IGNORE_RECURSION 1
#define IGNORE_THREADS 1
#define EXPLICIT_NONDET_LOCALS 0
#define FILTER_ASSERTIONS 1

twols_parse_optionst::twols_parse_optionst(int argc, const char **argv):
  parse_options_baset(TWOLS_OPTIONS, argc, argv),
  language_uit(cmdline, ui_message_handler),
  ui_message_handler(cmdline, "2LS " TWOLS_VERSION),
  recursion_detected(false),
  threads_detected(false),
  dynamic_memory_detected(false)
{
}

void twols_parse_optionst::eval_verbosity()
{
  // this is our default verbosity
  int v=messaget::M_STATISTICS;

  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2int(cmdline.get_value("verbosity"));
    if(v<0)
      v=0;
    else if(v>10)
      v=10;
  }

  ui_message_handler.set_verbosity(v);
}

void twols_parse_optionst::get_command_line_options(optionst &options)
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("xml-ui"))
    options.set_option("xml-ui", true);

  if(cmdline.isset("debug-level"))
    options.set_option("debug-level", cmdline.get_value("debug-level"));

  if(cmdline.isset("unwindset"))
    options.set_option("unwindset", cmdline.get_value("unwindset"));

  if(cmdline.isset("unwind"))
    options.set_option("unwind", cmdline.get_value("unwind"));

  if(cmdline.isset("inline-partial"))
    options.set_option("inline-partial", cmdline.get_value("inline-partial"));

  if(cmdline.isset("inline"))
    options.set_option("inline", true);

  if(cmdline.isset("slice") && cmdline.isset("inline"))
    options.set_option("slice", true);
  else
    options.set_option("slice", false);

  // all checks supported by goto_check
  PARSE_OPTIONS_GOTO_CHECK(cmdline, options);

  // check assertions
  if(cmdline.isset("no-assertions"))
    options.set_option("assertions", false);
  else
    options.set_option("assertions", true);

  // use assumptions
  if(cmdline.isset("no-assumptions"))
    options.set_option("assumptions", false);
  else
    options.set_option("assumptions", true);

  // use arithmetic refinements
  if(cmdline.isset("refine"))
    options.set_option("refine", true);
  else
    options.set_option("refine", false);

  // compute standard invariants (include value at loop entry)
  if(cmdline.isset("std-invariants"))
    options.set_option("std-invariants", true);
  else
    options.set_option("std-invariants", false);

  if(cmdline.isset("no-propagation"))
    options.set_option("constant-propagation", false);
  else
    options.set_option("constant-propagation", true);

  // magic error label
  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.get_value("error-label"));

  if(cmdline.isset("havoc"))
    options.set_option("havoc", true);
  else
  {
    // Options for using simple domains
    optionst::value_listt simple_domains;
    if(cmdline.isset("equalities"))
    {
      options.set_option("equalities", true);
      options.set_option("std-invariants", true);
      simple_domains.push_back("equalities");
    }
    if(cmdline.isset("heap"))
    {
      options.set_option("heap", true);
      simple_domains.push_back("heap");
    }

    // Choose only a single value domain
    if(cmdline.isset("values-refine"))
    {
      options.set_option("values-refine", true);
      options.set_option("intervals", true);
      simple_domains.push_back("intervals");
    }
    else if(cmdline.isset("zones"))
    {
      options.set_option("zones", true);
      simple_domains.push_back("zones");
    }
    else if(cmdline.isset("qzones"))
    {
      options.set_option("qzones", true);
      simple_domains.push_back("qzones");
    }
    else if(cmdline.isset("octagons"))
    {
      options.set_option("octagons", true);
      simple_domains.push_back("octagons");
    }
    else if(cmdline.isset("intervals"))
    {
      options.set_option("intervals", true);
      simple_domains.push_back("intervals");
    }

    // If no simple domains are specified, use intervals
    if(simple_domains.empty())
    {
      options.set_option("intervals", true);
      simple_domains.push_back("intervals");
    }

    // TODO: due to various modifications of options during verification
    //  (e.g. in summary_checker_ait or in handle_special_functions), it is not
    //  possible to rely on the content of this option.
    options.set_option("simple-domains", simple_domains);

    if(options.get_bool_option("values-refine") ||
       options.get_bool_option("zones") ||
       options.get_bool_option("qzones") ||
       options.get_bool_option("octagons") ||
       options.get_bool_option("intervals"))
    {
      // Choose solver for numerical domains
      if(cmdline.isset("enum-solver"))
        options.set_option("enum-solver", true);
      else // if(cmdline.isset("binsearch-solver")) // default
        options.set_option("binsearch-solver", true);
    }
  }

  // Heap domain requires full program inlining
  if(cmdline.isset("heap"))
    options.set_option("inline", true);

  // use incremental assertion checks
  if(cmdline.isset("non-incremental"))
    options.set_option("incremental", false);
  else
    options.set_option("incremental", true);

  // compute preconditions
  if(cmdline.isset("preconditions"))
    options.set_option("preconditions", true);

  // compute necessary/sufficient preconditions
  if(cmdline.isset("sufficient"))
    options.set_option("sufficient", true);

  // compute ranking functions
  if(cmdline.isset("termination"))
  {
    options.set_option("termination", true);
    options.set_option("sufficient", true);
    options.set_option("std-invariants", true);
  }

  if(cmdline.isset("monolithic-ranking-function"))
  {
    options.set_option("monolithic-ranking-function", true);
  }
  else
    options.set_option("monolithic-ranking-function", false);

  if(cmdline.isset("lexicographic-ranking-function"))
  {
    options.set_option(
      "lexicographic-ranking-function",
      cmdline.get_value("lexicographic-ranking-function"));
  }
  else
    options.set_option("lexicographic-ranking-function", 5);

  if(cmdline.isset("max-inner-ranking-iterations"))
  {
    options.set_option(
      "max-inner-ranking-iterations",
      cmdline.get_value("max-inner-ranking-iterations"));
  }
  else
    options.set_option("max-inner-ranking-iterations", 50);

  // do k-induction refinement
  if(cmdline.isset("k-induction"))
  {
    options.set_option("std-invariants", true);
    options.set_option("k-induction", true);
    options.set_option("inline", true);
    if(!cmdline.isset("unwind"))
      options.set_option("unwind", std::numeric_limits<unsigned>::max());
  }

  // compute singleton recurrence set - simple nontermination
  if(cmdline.isset("nontermination"))
  {
    options.set_option("nontermination", true);
    options.set_option("all-properties", true);
    options.set_option("inline", true);
    if(!cmdline.isset("unwind"))
      options.set_option("unwind", std::numeric_limits<unsigned>::max());
  }

  // do incremental bmc
  if(cmdline.isset("incremental-bmc"))
  {
    options.set_option("incremental-bmc", true);
    options.set_option("inline", true);
    options.set_option("havoc", true);
    if(!cmdline.isset("unwind"))
      options.set_option("unwind", std::numeric_limits<unsigned>::max());
  }

  // check for spuriousness of assertion failures
  if(cmdline.isset("no-spurious-check"))
    options.set_option("spurious-check", false);
  else
    options.set_option("spurious-check", true);

  // all properties (default)
  if(cmdline.isset("stop-on-fail"))
    options.set_option("all-properties", false);
  else
    options.set_option("all-properties", true);

  // no all functions (default)
  if(cmdline.isset("all-functions"))
    options.set_option("all-functions", true);
  else
    options.set_option("all-functions", false);

  // competition mode
  if(cmdline.isset("competition-mode"))
  {
    options.set_option("competition-mode", true);
    options.set_option("all-properties", false);
    options.set_option("inline", true);
    options.set_option("give-up-invariants", "2");
  }

  // instrumentation / output
  if(cmdline.isset("instrument-output"))
    options.set_option(
      "instrument-output",
      cmdline.get_value("instrument-output"));


#ifdef SHOW_CALLING_CONTEXTS
  if(cmdline.isset("show-calling-contexts"))
  {
    if(!options.get_bool_option("intervals"))
      throw "--show-calling-contexts only possible with --intervals";
    options.set_option("show-calling-contexts", true);
    options.set_option(
      "do-not-analyze-functions",
      cmdline.get_value("show-calling-contexts"));
  }
#endif

  if(cmdline.isset("trace"))
    options.set_option("trace", true);
  if(cmdline.isset("graphml-witness"))
    options.set_option("graphml-witness", cmdline.get_value("graphml-witness"));
  if(cmdline.isset("json-cex"))
    options.set_option("json-cex", cmdline.get_value("json-cex"));
}

/// invoke main modules
int twols_parse_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << TWOLS_VERSION << std::endl;
    return 0;
  }

  //
  // command line options
  //

  optionst options;
  get_command_line_options(options);

  eval_verbosity();

  //
  // Print a banner
  //
  status() << "2LS version " TWOLS_VERSION " (based on CBMC " CBMC_VERSION ")"
           << eom;

  goto_modelt goto_model;

  register_languages();

  if(get_goto_program(options, goto_model))
    return 6;

  if(cmdline.isset("heap") && dynamic_memory_detected)
  {
    // Only use sympath domain if dynamic memory is used
    options.set_option("sympath", true);
  }

  const namespacet ns(goto_model.symbol_table);

  if(cmdline.isset("show-stats"))
  {
    show_stats(goto_model, std::cout);
    return 7;
  }

  // options for various debug outputs

  if(cmdline.isset("show-ssa"))
  {
    bool simplify=!cmdline.isset("no-simplify");
    irep_idt function=cmdline.get_value("function");
    show_ssa(
      goto_model,
      options,
      function,
      simplify,
      std::cout,
      ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-defs"))
  {
    irep_idt function=cmdline.get_value("function");
    show_defs(goto_model, function, options, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-assignments"))
  {
    irep_idt function=cmdline.get_value("function");
    show_assignments(
      goto_model, function, options, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-guards"))
  {
    irep_idt function=cmdline.get_value("function");
    show_guards(goto_model, function, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-value-sets"))
  {
    irep_idt function=cmdline.get_value("function");
    show_value_sets(
      goto_model, function, options, std::cout, ui_message_handler);
    return 7;
  }

  if(cmdline.isset("show-invariants"))
  {
    options.set_option("show-invariants", true);
  }

  if(cmdline.isset("nontermination"))
  {
    // turn assertions (from generic checks) into assumptions
    Forall_goto_functions(f_it, goto_model.goto_functions)
    {
      goto_programt &body=f_it->second.body;
      Forall_goto_program_instructions(i_it, body)
      {
        if(i_it->is_assert())
          i_it->type=goto_program_instruction_typet::ASSUME;
      }
    }
  }

#if IGNORE_RECURSION
  if(recursion_detected)
  {
    status() << "Recursion not supported" << eom;
    report_unknown();
    return 5;
  }
#endif

#if IGNORE_THREADS
  if(threads_detected)
  {
    status() << "Threads not supported" << eom;
    report_unknown();
    return 5;
  }
#endif

  if(cmdline.isset("context-sensitive"))
  {
    options.set_option("context-sensitive", true);
    status() << "Context-sensitive analysis from " <<
      goto_model.goto_functions.entry_point() << eom;
  }

  if(cmdline.isset("arrays"))
  {
    options.set_option("arrays", true);
    status() << "Do not ignore array contents" << eom;
  }

  // TODO: check option inconsistencies, ignored options etc
  if(options.get_bool_option("havoc"))
    status() << "Havocking loops and function calls" << eom;
  else if(options.get_bool_option("equalities"))
    status() << "Using (dis)equalities domain" << eom;
  else if(options.get_bool_option("heap"))
    status() << "Using heap domain" << eom;
  else if(options.get_bool_option("heap-interval"))
    status() << "Using heap domain with interval domain for values" << eom;
  else if(options.get_bool_option("heap-zones"))
    status() << "Using heap domain with zones domain for values" << eom;
  else
  {
    if(options.get_bool_option("intervals"))
      status() << "Using intervals domain";
    else if(options.get_bool_option("zones"))
      status() << "Using zones domain";
    else if(options.get_bool_option("octagons"))
      status() << "Using octagons domain";
    else
      assert(false);

    if(options.get_bool_option("enum-solver"))
      status() << " with enumeration solver";
    else if(options.get_bool_option("binsearch-solver"))
      status() << " with binary search solver";
    else
      assert(false);

    status() << eom;
  }

  // don't use k-induction with dynamic memory
  if(options.get_bool_option("competition-mode") &&
     options.get_bool_option("k-induction") &&
     dynamic_memory_detected)
  {
    options.set_option("k-induction", false);
    options.set_option("std-invariants", false);
    options.set_option("incremental-bmc", false);
    options.set_option("unwind", 0);
  }
  // don't do nontermination with dynamic memory
  if(options.get_bool_option("competition-mode") &&
     (options.get_bool_option("termination") ||
      options.get_bool_option("nontermination")) &&
     dynamic_memory_detected)
  {
    error() << "Termination analysis does not support "
            << "dynamic memory allocation" << eom;
    report_unknown();
    return 5;
  }

  try
  {
    std::unique_ptr<summary_checker_baset> checker;
    if(!options.get_bool_option("k-induction") &&
       !options.get_bool_option("incremental-bmc"))
      checker=std::unique_ptr<summary_checker_baset>(
        new summary_checker_ait(options));
    if(options.get_bool_option("k-induction") &&
       !options.get_bool_option("incremental-bmc"))
      checker=std::unique_ptr<summary_checker_baset>(
        new summary_checker_kindt(options));
    if(!options.get_bool_option("k-induction") &&
       options.get_bool_option("incremental-bmc"))
      checker=std::unique_ptr<summary_checker_baset>(
        new summary_checker_bmct(options));
    if(options.get_bool_option("nontermination"))
      checker=std::unique_ptr<summary_checker_baset>(
        new summary_checker_nontermt(options));

    checker->set_message_handler(get_message_handler());
    checker->simplify=!cmdline.isset("no-simplify");
    checker->fixed_point=!cmdline.isset("no-fixed-point");

    int retval;
    if(cmdline.isset("show-vcc"))
    {
      std::cout << "VERIFICATION CONDITIONS:\n\n";
      checker->show_vcc=true;
      (*checker)(goto_model);
      return 0;
    }

    if(cmdline.isset("horn-encoding"))
    {
      status() << "Horn-clause encoding" << eom;
      namespacet ns(symbol_table);

      std::string out_file=cmdline.get_value("horn-encoding");

      if(out_file=="-")
      {
        horn_encoding(goto_model, options, std::cout);
      }
      else
      {
#ifdef _MSC_VER
        std::ofstream out(widen(out_file).c_str());
#else
        std::ofstream out(out_file.c_str());
#endif

        if(!out)
        {
          error() << "Failed to open output file "
                  << out_file << eom;
          return 1;
        }

        horn_encoding(goto_model, options, out);
      }

      return 0;
    }

    bool report_assertions=
      !options.get_bool_option("preconditions") &&
      !options.get_bool_option("termination") &&
      !options.get_bool_option("nontermination");
    // do actual analysis
    switch((*checker)(goto_model))
    {
    case property_checkert::resultt::PASS:
      if(report_assertions)
        report_properties(options, goto_model, checker->property_map);
      report_success();
      if(cmdline.isset("graphml-witness"))
        output_graphml_proof(options, goto_model, *checker);
      retval=0;
      break;

    case property_checkert::resultt::FAIL:
    {
      if(report_assertions)
        report_properties(options, goto_model, checker->property_map);

      // validate trace
      bool trace_valid=false;
      for(const auto &p : checker->property_map)
      {
        if(p.second.result!=property_checkert::resultt::FAIL)
          continue;

        if(options.get_bool_option("trace"))
          show_counterexample(goto_model, p.second.error_trace);

        trace_valid=
          !p.second.error_trace.steps.empty() &&
          (options.get_bool_option("nontermination") ||
           p.second.error_trace.steps.back().is_assert());
        break;
      }

      if(cmdline.isset("graphml-witness"))
      {
#if 1
        if(!trace_valid)
        {
          retval=5;
          error() << "Internal witness validation failed" << eom;
          report_unknown();
          break;
        }
#endif
        output_graphml_cex(options, goto_model, *checker);
      }
      report_failure();
      retval=10;
      break;
    }
    case property_checkert::resultt::UNKNOWN:
      if(report_assertions)
        report_properties(options, goto_model, checker->property_map);
      retval=5;
      report_unknown();
      break;

    default:
      assert(false);
    }

    if(cmdline.isset("instrument-output"))
    {
      checker->instrument_and_output(
        goto_model,
        ui_message_handler.get_verbosity());
    }

    return retval;
  }

  catch(const std::string error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

  catch(const char *error_msg)
  {
    error() << error_msg << messaget::eom;
    return 8;
  }

#if 0
  // let's log some more statistics
  debug() << "Memory consumption:" << messaget::endl;
  memory_info(debug());
  debug() << eom;
#endif
}

void twols_parse_optionst::type_stats_rec(
  const typet &type,
  expr_statst &stats,
  const namespacet &ns)
{
  if(type.id()==ID_symbol)
    type_stats_rec(ns.follow(type), stats, ns);

  if(type.id()==ID_pointer || type.id()==ID_array)
  {
    stats.has_array=true;

    const typet &subtype=ns.follow(type.subtype());

    if(subtype.id()==ID_signedbv ||
       subtype.id()==ID_unsignedbv)
    {
      stats.has_string=
        (to_bitvector_type(subtype).get_width()==config.ansi_c.char_width);
    }
  }

  if(type.has_subtypes())
  {
    forall_subtypes(it, type)
    {
      type_stats_rec(*it, stats, ns);
    }
  }
}

void twols_parse_optionst::expr_stats_rec(
  const exprt &expr,
  expr_statst &stats)
{
  if(expr.id()==ID_side_effect)
  {
    const side_effect_exprt &side_effect_expr=to_side_effect_expr(expr);
    const irep_idt &statement=side_effect_expr.get_statement();

    if(statement==ID_malloc)
    {
      stats.has_malloc=true;
    }
    else if(statement==ID_nondet)
    {
      // done in statet:instantiate_rec
    }
  }

  if(expr.has_operands())
  {
    forall_operands(it, expr)
    {
      expr_stats_rec(*it, stats);
    }
  }
}


void twols_parse_optionst::show_stats(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  const namespacet ns(goto_model.symbol_table);

  expr_statst stats;

  unsigned nr_instructions=0;
  unsigned nr_functions=0;
  unsigned nr_loops=0;

  // analyze all the functions
  forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(!f_it->second.body_available())
      continue;

    ++nr_functions;

    const goto_programt &goto_program=f_it->second.body;

#if 0
    statistics() << "function size of " << f_it->first << ": "
                 << goto_program.instructions.size() << eom;
#endif

    for(goto_programt::instructionst::const_iterator
          i_it=goto_program.instructions.begin();
        i_it!=goto_program.instructions.end();
        i_it++)
    {
      nr_instructions++;
      const goto_programt::instructiont &instruction=*i_it;

      if(i_it->is_backwards_goto())
        nr_loops++;

      switch(instruction.type)
      {
      case ASSIGN:
      {
        const code_assignt &assign=to_code_assign(instruction.code);
        expr_stats_rec(assign.lhs(), stats);
        expr_stats_rec(assign.rhs(), stats);
        break;
      }
      case ASSUME:
        expr_stats_rec(instruction.guard, stats);
        break;
      case ASSERT:
        expr_stats_rec(instruction.guard, stats);
        break;
      case GOTO:
        expr_stats_rec(instruction.guard, stats);
        break;

      case DECL:
        // someone declaring an array
        type_stats_rec(
          to_code_decl(instruction.code).symbol().type(), stats, ns);

        break;

      default:
        // skip
        break;
      } // switch
    } // forall instructions
  } // forall functions

  out << "=============== STATS=============== " << std::endl;
  out << "  nr of instructions: " << nr_instructions << std::endl;
  out << "  nr of functions: " << nr_functions << std::endl;
  out << "  nr of loops: " << nr_loops << std::endl;
  out << "  malloc: " << (stats.has_malloc ? "YES" : "NO") << std::endl;
  out << "  arrays: " << (stats.has_array ? "YES" : "NO") << std::endl;
  out << "  strings: " << (stats.has_string ? "YES" : "NO") << std::endl;
}


bool twols_parse_optionst::set_properties(goto_modelt &goto_model)
{
  try
  {
    if(cmdline.isset("property"))
      ::set_properties(goto_model, cmdline.get_values("property"));
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  return false;
}

void twols_parse_optionst::require_entry(
  const goto_modelt &goto_model)
{
  irep_idt entry_point=goto_model.goto_functions.entry_point();

  if(goto_model.symbol_table.symbols.find(entry_point)==
     symbol_table.symbols.end())
    throw "the program has no entry point; please complete linking";
}

bool twols_parse_optionst::get_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  if(cmdline.args.size()==0)
  {
    error() << "Please provide a program to verify" << eom;
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(cmdline.args[0]))
    {
      status() << "Reading GOTO program from file" << eom;

      if(read_goto_binary(
           cmdline.args[0], goto_model, get_message_handler()))
        return true;

      config.set_from_symbol_table(goto_model.symbol_table);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }
    }
    else if(cmdline.isset("show-parse-tree"))
    {
      if(cmdline.args.size()!=1)
      {
        error() << "Please give one source file only" << eom;
        return true;
      }

      std::string filename=cmdline.args[0];

#ifdef _MSC_VER
      std::ifstream infile(widen(filename).c_str());
#else
      std::ifstream infile(filename.c_str());
#endif

      if(!infile)
      {
        error() << "failed to open input file `" << filename << "'" << eom;
        return true;
      }

      languaget *language=get_language_from_filename(filename);

      if(language==NULL)
      {
        error() << "failed to figure out type of file `" << filename << "'"
                << eom;
        return true;
      }

      language->set_message_handler(get_message_handler());

      status() << "Parsing" << filename << eom;

      if(language->parse(infile, filename))
      {
        error() << "PARSING ERROR" << eom;
        return true;
      }

      language->show_parse(std::cout);
      return true;
    }
    else
    {
      if(parse())
        return true;
      if(typecheck())
        return true;
      if(final())
        return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

#if 0
      irep_idt entry_point=goto_model.goto_functions.entry_point();

      if(symbol_table.symbols.find(entry_point)==symbol_table.symbols.end())
      {
        error() << "No entry point; please provide a main function" << eom;
        return true;
      }
#endif

      status() << "Generating GOTO Program" << eom;

      goto_convert(symbol_table, goto_model, ui_message_handler);
    }

    // finally add the library
    status() << "Adding CPROVER library" << eom;
    link_to_library(goto_model, ui_message_handler);

    if(process_goto_program(options, goto_model))
      return true;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

bool twols_parse_optionst::process_goto_program(
  const optionst &options,
  goto_modelt &goto_model)
{
  try
  {
    status() << "Function Pointer Removal" << eom;
    remove_function_pointers(
      get_message_handler(),
      goto_model,
      cmdline.isset("pointer-check"));

    // do partial inlining
    if(options.get_bool_option("inline-partial"))
    {
      unsigned limit=options.get_unsigned_int_option("inline-partial");
      status() << "Performing partial inlining (" << limit << ")" << eom;
      goto_partial_inline(goto_model, ui_message_handler, limit/2);
      // TODO: where is limit multiplied by 2???

      // remove inlined functions
      Forall_goto_functions(f_it, goto_model.goto_functions)
        if(f_it->first!=goto_functionst::entry_point() &&
           f_it->second.body.instructions.size()<=2*(limit/2))
        {
          f_it->second.body.clear();
        }
    }

#if IGNORE_THREADS
    threads_detected=has_threads(goto_model);
#endif

    // remove returns (must be done after function pointer removal)
    remove_returns(goto_model);

    if(options.get_bool_option("competition-mode"))
      assert_no_atexit(goto_model);

    // now do full inlining, if requested
    if(options.get_bool_option("inline"))
    {
      status() << "Performing full inlining" << eom;
      const namespacet ns(goto_model.symbol_table);
      goto_inlinet goto_inline(
        goto_model.goto_functions,
        ns,
        ui_message_handler,
        false);
      goto_inline();
#if IGNORE_RECURSION
      recursion_detected=goto_inline.recursion_detected();
      // since CBMC 5.7, inlining doesn't update location and loop numbers
      goto_model.goto_functions.update();
      goto_model.goto_functions.compute_loop_numbers();
#endif
    }

    if(options.get_bool_option("competition-mode"))
      assert_no_builtin_functions(goto_model);

#if REMOVE_MULTIPLE_DEREFERENCES
    remove_multiple_dereferences(goto_model);
#endif

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(options, goto_model);

#if UNWIND_GOTO_INTO_LOOP
    unwind_goto_into_loop(goto_model, 2);
#else
    if(unwind_goto_into_loop(goto_model, 2))
    {
      status() << "Irreducible control flow not supported" << eom;
      report_unknown();
      return 5;
    }
#endif

    remove_skip(goto_model.goto_functions);
    goto_model.goto_functions.update();

    // preprocessing to improve the structure of the SSA for the unwinder
    split_loopheads(goto_model);

#if EXPLICIT_NONDET_LOCALS
    // explicitly initialize all local variables
    nondet_locals(goto_model);
#endif

#if 1
    // Find, inline and remove malloc function
    // TODO: find a better place for that
    Forall_goto_functions(it, goto_model.goto_functions)
    {
      if(it->first=="malloc" || it->first=="free")
        it->second.type.set(ID_C_inlined, true);
    }
    goto_partial_inline(goto_model, ui_message_handler, 0);
    Forall_goto_functions(it, goto_model.goto_functions)
    {
      if(it->first=="malloc" || it->first=="free")
        it->second.body.clear();
    }
#endif

    // create symbols for objects pointed by parameters
    create_dynamic_objects(goto_model);

#if REMOVE_MULTIPLE_DEREFERENCES
    remove_multiple_dereferences(goto_model);
#endif

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();

    // Replace malloc
    dynamic_memory_detected=replace_malloc(
      goto_model, "", options.get_bool_option("pointer-check"));

    // Allow recording of mallocs and memory leaks
    if(options.get_bool_option("pointer-check"))
    {
      allow_record_malloc(goto_model);
      handle_freed_ptr_compare(goto_model);
    }
    if(options.get_bool_option("memory-leak-check"))
      allow_record_memleak(goto_model);

    split_same_symbolic_object_assignments(goto_model);

    // remove loop heads from function entries
    remove_loops_in_entry(goto_model);

    // inline __CPROVER_initialize and main
    if(cmdline.isset("inline-main"))
    {
      inline_main(goto_model);
    }

    auto dynobj_instances=split_dynamic_objects(goto_model, options);

    if(!cmdline.isset("independent-properties"))
    {
      add_assumptions_after_assertions(goto_model);
    }

#ifdef FILTER_ASSERTIONS
    filter_assertions(goto_model);
#endif

    if(options.get_bool_option("constant-propagation"))
    {
      status() << "Constant Propagation" << eom;
      propagate_constants(goto_model);
    }

    remove_dead_goto(goto_model);

    if(cmdline.isset("competition-mode"))
    {
      limit_array_bounds(goto_model);
      if(options.get_bool_option("memory-leak-check"))
        memory_assert_info(goto_model);
    }

    // if we aim to cover, replace
    // all assertions by false to prevent simplification
    if(cmdline.isset("cover-assertions"))
      make_assertions_false(goto_model);

    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(get_ui(), goto_model);
      return true;
    }

    label_properties(goto_model);

    if(cmdline.isset("show-properties"))
    {
      show_properties(goto_model, get_ui());
      return true;
    }

    if(set_properties(goto_model))
      return true;

    // show it?
    if(cmdline.isset("show-goto-functions"))
    {
      const namespacet ns(goto_model.symbol_table);
      goto_model.goto_functions.output(ns, std::cout);
      return true;
    }
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string e)
  {
    error() << e << eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    error() << "Out of memory" << eom;
    return true;
  }

  return false;
}

void twols_parse_optionst::report_properties(
  const optionst &options,
  const goto_modelt &goto_model,
  const property_checkert::property_mapt &property_map)
{
  for(property_checkert::property_mapt::const_iterator
        it=property_map.begin();
      it!=property_map.end();
      it++)
  {
#if 1
    // TODO: some properties do not show up in initialize_property_map
    if(it->first=="")
      continue;
#endif

    if(!options.get_bool_option("all-properties") &&
       it->second.result!=property_checkert::resultt::FAIL)
      continue;

    if(get_ui()==ui_message_handlert::uit::XML_UI)
    {
      xmlt xml_result("result");
      xml_result.set_attribute("property", id2string(it->first));
      xml_result.set_attribute(
        "status",
        property_checkert::as_string(it->second.result));
      std::cout << xml_result << "\n";
    }
    else
    {
      status() << "[" << it->first << "] "
               << it->second.location->source_location.get_comment()
               << ": "
               << property_checkert::as_string(it->second.result)
               << eom;
    }

    if(options.get_bool_option("trace") &&
       it->second.result==property_checkert::resultt::FAIL)
      show_counterexample(goto_model, it->second.error_trace);
    if(cmdline.isset("json-cex") &&
       it->second.result==property_checkert::resultt::FAIL)
      output_json_cex(
        options,
        goto_model,
        it->second.error_trace,
        id2string(it->first));
  }

  if(!cmdline.isset("property"))
  {
    status() << eom;

    unsigned failed=0;
    unsigned unknown=0;

    for(property_checkert::property_mapt::const_iterator
          it=property_map.begin();
        it!=property_map.end();
        it++)
    {
      if(it->second.result==property_checkert::resultt::UNKNOWN)
        unknown++;
      if(it->second.result==property_checkert::resultt::FAIL)
        failed++;
    }

    status() << "** " << unknown
             << " of " << property_map.size() << " unknown"
             << eom;
    status() << "** " << failed
             << " of " << property_map.size() << " failed"
             << eom;
  }
}

void twols_parse_optionst::report_success()
{
  result() << "VERIFICATION SUCCESSFUL" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data="SUCCESS";
    std::cout << xml;
    std::cout << std::endl;
    break;
  }

  default:
    assert(false);
  }
}

void twols_parse_optionst::show_counterexample(
  const goto_modelt &goto_model,
  const goto_tracet &error_trace)
{
  const namespacet ns(goto_model.symbol_table);

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    std::cout << std::endl << "Counterexample:" << std::endl;
    show_goto_trace(std::cout, ns, error_trace);
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml;
    convert(ns, error_trace, xml);
    std::cout << xml << std::endl;
  }
  break;

  default:
    assert(false);
  }
}

void twols_parse_optionst::output_graphml_cex(
  const optionst &options,
  const goto_modelt &goto_model,
  const summary_checker_baset &summary_checker)
{
  for(const auto &p : summary_checker.property_map)
  {
    if(p.second.result!=property_checkert::resultt::FAIL)
      continue;

    const namespacet ns(goto_model.symbol_table);
    const std::string graphml=options.get_option("graphml-witness");
    if(!graphml.empty())
    {
      graphml_witnesst graphml_witness(ns);
      graphml_witness(p.second.error_trace);

      if(graphml=="-")
        write_graphml(graphml_witness.graph(), std::cout);
      else
      {
        std::ofstream out(graphml.c_str());
        write_graphml(graphml_witness.graph(), out);
      }
    }
    break;
  }
}

void twols_parse_optionst::output_graphml_proof(
  const optionst &options,
  const goto_modelt &goto_model,
  const summary_checker_baset &summary_checker)
{
  const namespacet ns(goto_model.symbol_table);
  const std::string graphml=options.get_option("graphml-witness");
  if(!graphml.empty())
  {
    graphml_witness_extt graphml_witness(ns);
    graphml_witness(summary_checker);

    if(graphml=="-")
      write_graphml(graphml_witness.graph(), std::cout);
    else
    {
      std::ofstream out(graphml.c_str());
      write_graphml(graphml_witness.graph(), out);
    }
  }
}
void twols_parse_optionst::output_json_cex(
  const optionst &options,
  const goto_modelt &goto_model,
  const goto_tracet &error_trace,
  const std::string &property_id)
{
  if(options.get_option("json-cex")!="")
  {
    const namespacet ns(goto_model.symbol_table);
    jsont json_trace;
    convert(ns, error_trace, json_trace);

    if(options.get_option("json-cex")=="-")
    {
      std::cout << json_trace;
    }
    else
    {
      std::ofstream out(
        (options.get_option("json-cex")+"-"+property_id+".json").c_str());
      out << json_trace << '\n';
    }
  }
}

void twols_parse_optionst::report_failure()
{
  result() << "VERIFICATION FAILED" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data="FAILURE";
    std::cout << xml;
    std::cout << std::endl;
  }
  break;

  default:
    assert(false);
  }
}

void twols_parse_optionst::report_unknown()
{
  result() << "VERIFICATION INCONCLUSIVE" << eom;

  switch(get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml("cprover-status");
    xml.data="UNKNOWN";
    std::cout << xml;
    std::cout << std::endl;
  }
  break;

  default:
    assert(false);
  }
}

/// display command line help
void twols_parse_optionst::help()
{
  std::cout <<
    "\n"
    "* *  2LS " TWOLS_VERSION "-Copyright (C) 2014-2017                    * *\n" // NOLINT(*)
    "* *  (based on CBMC " CBMC_VERSION " ";
  std::cout << "(" << (sizeof(void *)*8) << "-bit version))";

  std::cout << "                   * *\n";

  std::cout <<
    "* *           Daniel Kroening, Peter Schrammel              * *\n"
    "* *                 University of Oxford                    * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "\n"
    "Usage:                        Purpose:\n"
    "\n"
    " 2ls [-?] [-h] [--help] show help\n"
    " 2ls file.c ...               source file names\n"
    "\n"
    "Frontend options:\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --preprocess                 stop after preprocessing\n"
    " --16, --32, --64             set width of int\n"
    " --LP64, --ILP64, --LLP64, \n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              allow little-endian word-byte conversions\n"
    " --big-endian                 allow big-endian word-byte conversions\n"
    " --unsigned-char              make \"char\" unsigned by default\n"
    " --show-stats                 show statistics about program\n"
    " --show-parse-tree            show parse tree\n"
    " --show-symbol-table          show symbol table\n"
    " --show-goto-functions        show goto program\n"
    " --arch                       set architecture (default: " << configt::this_architecture() << ")\n" // NOLINT(*)
    " --os                         set operating system (default: " << configt::this_operating_system() << ")\n" // NOLINT(*)
#ifdef _WIN32
    " --gcc                        use GCC as preprocessor\n"
#endif
    " --no-arch                    don't set up an architecture\n"
    " --no-library                 disable built-in abstract C library\n"
    " --round-to-nearest           IEEE floating point rounding mode (default)\n" // NOLINT(*)
    " --round-to-plus-inf          IEEE floating point rounding mode\n"
    " --round-to-minus-inf         IEEE floating point rounding mode\n"
    " --round-to-zero              IEEE floating point rounding mode\n"
    "\n"
    "Program instrumentation options:\n"
    HELP_GOTO_CHECK
    " --error-label label          check that label is unreachable\n"
    " --show-properties            show the properties\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --inline                     inline all functions into main\n"
    " --inline-partial nr          inline functions smaller than the given nr of instructions\n" // NOLINT(*)
    " --instrument-output outfile  instrument GOTO code with invariants and export it to outfile\n" // NOLINT(*)
    "\n"
    "Backend options:\n"
    " --all-functions              check each function as entry point\n"
    " --stop-on-fail               stop on first failing assertion\n"
    " --trace                      give a counterexample trace for failed properties\n" //NOLINT(*)
    " --context-sensitive          context-sensitive analysis from entry point\n" // NOLINT(*)
    " --termination                compute ranking functions to prove termination\n" // NOLINT(*)
    " --k-induction                use k-induction\n"
    " --incremental-bmc            use incremental-bmc\n"
    " --preconditions              compute preconditions\n"
    " --sufficient                 sufficient preconditions (default: necessary)\n" // NOLINT(*)
    " --havoc                      havoc loops and function calls\n"
    " --intervals                  use interval domain\n"
    " --equalities                 use equalities and disequalities domain\n"
    " --heap                       use heap domain\n"
    " --zones                      use zone domain\n"
    " --octagons                   use octagon domain\n"
    " --values-refine              use dynamic refinement of strength of the value domain\n" // NOLINT(*)
    " --sympath                    compute invariant for each symbolic path\n"
    "                              (only usable with --heap-* switches)\n"
    " --enum-solver                use solver based on model enumeration\n"
    " --binsearch-solver           use solver based on binary search\n"
    " --arrays                     do not ignore array contents\n"
    " --lexicographic-ranking-function n          (default n=3)\n"
    " --monolithic-ranking-function\n"
    " --max-inner-ranking-iterations n           (default n=20)\n"
    "\n"
    "Other options:\n"
    " --version                    show version and exit\n"
    " --xml-ui                     use XML-formatted output\n"
    "\n";
}
