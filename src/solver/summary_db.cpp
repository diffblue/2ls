/*******************************************************************\

Module: Storage for Function Summaries

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Storage for Function Summaries

#include <fstream>

#include <json/json_parser.h>

#include "summary_db.h"

void summary_dbt::put(
  const function_namet &function_name,
  const summaryt &summary)
{
  if(store.find(function_name)==store.end() ||
     store[function_name].mark_recompute)
    store[function_name]=summary;
  else
    store[function_name].join(summary);
}

void summary_dbt::mark_recompute_all()
{
  for(std::map<function_namet, summaryt>::iterator it=store.begin();
      it!=store.end(); it++)
    it->second.mark_recompute=true;
}

std::string summary_dbt::file_name(const std::string &id)
{
  return "summary."+id;
}

void summary_dbt::read(const std::string &id)
{
  current=id;

  summary.make_object();

  parse_json(file_name(id), get_message_handler(), summary);
}

void summary_dbt::write()
{
  std::ofstream out(file_name(current).c_str());
  out << summary << '\n';
}
