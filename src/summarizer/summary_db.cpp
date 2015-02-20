/*******************************************************************\

Module: Storage for Function Summaries

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <json/json_parser.h>

#include "summary_db.h"

/*******************************************************************\

Function: summary_dbt::file_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string summary_dbt::file_name(const std::string &id)
{
  return "summary."+id;
}

/*******************************************************************\

Function: summary_dbt::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_dbt::read(const std::string &id)
{
  current=id;

  summary.clear();

  parse_json(file_name(id), get_message_handler(), summary);
}

/*******************************************************************\

Function: summary_dbt::write

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summary_dbt::write()
{
  std::ofstream out(file_name(current).c_str());
  out << summary;
}
