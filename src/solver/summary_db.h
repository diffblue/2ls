/*******************************************************************\

Module: Storage for Function Summaries

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Storage for Function Summaries

#ifndef CPROVER_2LS_SOLVER_SUMMARY_DB_H
#define CPROVER_2LS_SOLVER_SUMMARY_DB_H

#include "summary.h"
#include <util/message.h>
#include <util/json.h>

class summary_dbt:public messaget
{
public:
  typedef irep_idt function_namet;

  // retrieve a summary for function with given identifier
  void read(const std::string &);
  void write();
  void clear() { store.clear(); }

  summaryt get(const function_namet &function_name) const
    { return store.at(function_name); }
  bool exists(const function_namet &function_name) const
    { return store.find(function_name)!=store.end(); }
  void put(const function_namet &function_name, const summaryt &summary);

  void mark_recompute_all();

  jsont summary;

protected:
  std::map<function_namet, summaryt> store;

  std::string current;
  std::string file_name(const std::string &);
};

#endif
