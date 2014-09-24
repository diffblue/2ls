/*******************************************************************\

Module: Summarizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARY_CHECKER_H
#define CPROVER_SUMMARY_CHECKER_H

#include <util/time_stopping.h>

#include <goto-programs/property_checker.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/prop/cover_goals.h>

#include "../ssa/local_ssa.h"
#include "../ssa/ssa_unwinder.h"
#include "ssa_db.h"
#include "summary_db.h"
#include "summarizer.h"

class summary_checkert:public property_checkert
{
public:
  inline summary_checkert(optionst &_options):
    show_vcc(false),
    simplify(false),
    fixed_point(false),
    options(_options),
    ssa_db(),summary_db(),
    ssa_unwinder(ssa_db),
    summarizer(_options,summary_db,ssa_db,ssa_unwinder),
    solver_instances(0),
    solver_calls(0)
  {

  }
  
  bool show_vcc, simplify, fixed_point;

  virtual resultt operator()(const goto_modelt &);

  // statistics
  absolute_timet start_time;
  time_periodt sat_time;

protected:
  optionst &options;

  ssa_dbt ssa_db;
  summary_dbt summary_db;
  ssa_unwindert ssa_unwinder;
  summarizert summarizer;

  unsigned solver_instances;
  unsigned solver_calls;
  void report_statistics();

  void do_show_vcc(
    const local_SSAt &,
    const goto_programt::const_targett,
    const local_SSAt::nodet::assertionst::const_iterator &);

  void SSA_functions(const goto_modelt &, const namespacet &ns);

  void summarize(const goto_modelt &, bool forward=true, bool sufficient=false);

  property_checkert::resultt check_properties();
  void check_properties_non_incremental(const summarizert::functionst::const_iterator f_it);
  void check_properties_incremental(const summarizert::functionst::const_iterator f_it);

  exprt::operandst get_loophead_selects(const irep_idt &function_name, const local_SSAt &, prop_convt &);
  bool is_spurious(const exprt::operandst& loophead_selects, prop_convt&);

  void report_preconditions();


  //cover goals extended with spuriousness check

  struct goalt
  {
    // a property holds if all instances of it are true
    exprt::operandst conjuncts;
    std::string description;

    explicit goalt(const goto_programt::instructiont &instruction)
      {
	description=id2string(instruction.source_location.get_comment());
      }
  
    goalt()
      {
      }
  };

  class cover_goals_extt : public cover_goalst
  {
    public:
      explicit inline cover_goals_extt(prop_convt &_prop_conv,
				       const exprt::operandst& _loophead_selects,
	property_mapt &_property_map):
          cover_goalst(_prop_conv), 
          property_map(_property_map), 
	  loophead_selects(_loophead_selects),
	  activation_literal_counter(0)
          {}

      typedef std::map<irep_idt, goalt> goal_mapt;
      goal_mapt goal_map;

    protected:
      property_mapt &property_map;
      exprt::operandst loophead_selects;
      unsigned activation_literal_counter;

      virtual void assignment();
  };

};

#endif
