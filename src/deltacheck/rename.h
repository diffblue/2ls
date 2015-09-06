/*******************************************************************\

Module: Symbol Renaming

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_RENAME_H
#define CPROVER_DELTACHECK_RENAME_H

#include <util/symbol_table.h>
#include <goto-programs/goto_functions.h>

class renamet
{
public:
  renamet():suffix("$old")
  {
  }

  void operator()(symbol_tablet &);
  void operator()(symbolt &);
  void operator()(exprt &);
  void operator()(typet &);
  void operator()(goto_functionst &);
  void operator()(goto_functionst::goto_functiont &);
  
  std::string suffix;

protected:
};

#endif
