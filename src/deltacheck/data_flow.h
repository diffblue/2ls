/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/goto_program.h>

#include "solver.h"

class data_flowt
{
public:
  data_flowt(solvert &_solver):
    version(0),
    assert_to_assume(false),
    solver(_solver)
  {
  }

  unsigned version;
  bool assert_to_assume;

  void operator()(const goto_programt &);
  
protected:
  solvert &solver;
  
  typedef enum { OUT, OUT_TAKEN, IN } kindt;
 
  exprt rename(kindt kind, const exprt &src, goto_programt::const_targett t);
  typet rename(kindt kind, const typet &src, goto_programt::const_targett t);
  
  void transformer(goto_programt::const_targett t);
  void skip_transformer(goto_programt::const_targett t);

  void collect_objects(const goto_programt &);
  void collect_objects(const exprt &);

  typedef std::set<exprt> objectst;
  objectst objects;  
  
  typedef std::vector<goto_programt::const_targett> work_queuet;
  work_queuet work_queue;
  
  struct loct
  {
    goto_programt::const_targetst succ, pred;
  };
  
  bool propagate(const loct &loc);
  
  typedef std::map<goto_programt::const_targett, loct> loc_mapt;
  loc_mapt loc_map;
};
