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

  virtual summaryt get(function_namet function_name) const 
    { return store.at(function_name); }
  virtual bool exists(function_namet function_name) const  
    { return store.find(function_name)!=store.end(); }
  virtual void put(function_namet function_name, summaryt summary) 
    { store[function_name] = summary; }

 protected:
  std::map<function_namet, summaryt> store;
};

#endif
