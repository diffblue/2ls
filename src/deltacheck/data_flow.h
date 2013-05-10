/*******************************************************************\

Module: Data Flow Analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/goto_program.h>

class data_flowt
{
public:
  data_flowt():version(0)
  {
  }

  unsigned version;

  void operator()(const goto_programt &);
  
protected:
  exprt rename_rhs(const exprt &src, goto_programt::const_targett t);
  exprt rename_lhs(const exprt &src, goto_programt::const_targett t);
};
