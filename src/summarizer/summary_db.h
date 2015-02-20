/*******************************************************************\

Module: Abstract Interface for a Function Summary

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SUMMARIZER_SUMMARY_DB_H
#define CPROVER_SUMMARIZER_SUMMARY_DB_H

#include <util/message.h>

#include <json/json.h>

class summary_dbt:public messaget
{
public:
  // retrieve a summary for function with given identifier
  void read(const std::string &);
  void write();
  
  jsont summary;

protected:
  std::string current;
  std::string file_name(const std::string &);
};

#endif
