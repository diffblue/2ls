/*******************************************************************\

Module: Cover a set of goals incrementally

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_COVER_GOALS_H
#define CPROVER_SUMMARIZER_COVER_GOALS_H

#include <util/message.h>
#include <goto-programs/property_checker.h>

#include "../domains/incremental_solver.h"

/*******************************************************************\

   Class: cover_gooalst

 Purpose: Try to cover some given set of goals incrementally.
          This can be seen as a heuristic variant of
          SAT-based set-cover. No minimality guarantee.

\*******************************************************************/

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

class cover_goals_extt:public messaget
{
public:
      explicit inline cover_goals_extt(incremental_solvert &_solver,
				   const exprt::operandst& _loophead_selects,
				   property_checkert::property_mapt &_property_map,
				   bool _spurious_check):
          solver(_solver), 
          property_map(_property_map), 
	  spurious_check(_spurious_check),
	  loophead_selects(_loophead_selects)
          {}
  
  virtual ~cover_goals_extt();

  void operator()();

  // the goals

  struct cover_goalt
  {
    literalt condition;
    bool covered;
    
    cover_goalt():covered(false)
    {
    }
  };

  typedef std::list<cover_goalt> goalst;
  goalst goals;
  
  typedef std::map<irep_idt,goalt> goal_mapt;
  goal_mapt goal_map;

  // statistics

  inline unsigned number_covered() const
  {
    return _number_covered;
  }
  
  inline unsigned iterations() const
  {
    return _iterations;
  }
  
  inline goalst::size_type size() const
  {
    return goals.size();
  }
  
  // managing the goals

  inline void add(const literalt condition)
  {
    goals.push_back(cover_goalt());
    goals.back().condition=condition;
  }
  
protected:
  unsigned _number_covered, _iterations;
  incremental_solvert &solver;
  property_checkert::property_mapt &property_map;
  bool spurious_check;
  exprt::operandst loophead_selects;

  // this method is called for each satisfying assignment
  virtual void assignment();

private:
  void mark();
  void constraint();
  void freeze_goal_variables();
};

#endif
