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

  virtual void load() const {}
  virtual void save() const {}
  virtual void clear() { store.clear(); }

  virtual summaryt get(const function_namet &function_name) const 
    { return store.at(function_name); }
  virtual bool exists(const function_namet &function_name) const  
    { return store.find(function_name)!=store.end(); }
  virtual void put(const function_namet &function_name, const summaryt &summary)
    { store[function_name] = summary; }

 protected:
  std::map<function_namet, summaryt> store;
};

#endif
