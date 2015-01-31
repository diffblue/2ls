/*******************************************************************\

Module: Storage for Function Summaries

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_SUMMARY_DB_H
#define CPROVER_SUMMARIZER_SUMMARY_DB_H

#include "summary.h"

class summary_dbt
{
public:
  typedef irep_idt function_namet;

  void load() const {}
  void save() const {}
  void clear() { store.clear(); }

  summaryt get(const function_namet &function_name) const 
    { return store.at(function_name); }
  bool exists(const function_namet &function_name) const  
    { return store.find(function_name)!=store.end(); }
  void put(const function_namet &function_name, const summaryt &summary);

  void mark_recompute_all();

 protected:
  std::map<function_namet, summaryt> store;
};

#endif
