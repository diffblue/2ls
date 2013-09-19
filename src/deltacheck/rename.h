/*******************************************************************\

Module: Symbol Renaming

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_RENAME_H
#define CPROVER_DELTACHECK_RENAME_H

#include <util/symbol_table.h>
#include <goto-programs/goto_functions.h>

void rename(symbol_tablet &);
void rename(exprt &);
void rename(typet &);
void rename(goto_functionst &);

#endif
