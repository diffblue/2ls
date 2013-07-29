/*******************************************************************\

Module: Property Management

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_PROPERTIES_H
#define DELTACHECK_PROPERTIES_H

#include <util/threeval.h>

#include "function_ssa.h"

class propertyt
{
public:
  goto_programt::const_targett loc;
  tvt status;
  exprt guard, condition;
  
  // in case of failed properties: countermodel
  typedef std::map<exprt, exprt> value_mapt;
  value_mapt value_map;
};
  
typedef std::list<propertyt> propertiest;

void report_properties(
  const propertiest &,
  std::ostream &);

void report_countermodels(
  const function_SSAt &,
  const propertiest &,
  std::ostream &);

void report_countermodels(
  const function_SSAt &function_SSA_old,
  const function_SSAt &function_SSA_new,
  const propertiest &,
  std::ostream &);

#endif
