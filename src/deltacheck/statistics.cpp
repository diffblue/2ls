/*******************************************************************\

Module: Statistics

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "statistics.h"
#include "html_escape.h"

/*******************************************************************\

Function: statisticst::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::clear()
{
  time_map.clear();
  functions_processed=0;
}

/*******************************************************************\

Function: statisticst::start

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::start(const std::string &what)
{
  timet &t=time_map[what];
  assert(!t.running);
  t.start=current_time();
  t.running=true;
}

/*******************************************************************\

Function: statisticst::stop

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::stop(const std::string &what)
{
  timet &t=time_map[what];
  assert(t.running);
  fine_timet this_period=current_time()-t.start;
  t.function=this_period;
  t.total+=this_period;
  t.running=false;
}

/*******************************************************************\

Function: statisticst::html_report_total

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::html_report_total(std::ostream &out) const
{
  out << "<p class=\"total_statistics\">\n";
  
  out << "<table>\n";
  
  out << "<tr><td>Functions:</td><td>" << functions_processed
      << "</td></tr>\n";

  for(time_mapt::const_iterator
      it=time_map.begin(); it!=time_map.end(); it++)
  {
    out << "<tr><td>";
    out << html_escape(it->first) << ":</td><td>"
        << it->second.function
        << "s</td></tr>\n";
  }
  
  out << "</table>\n";
  
  out << "</p>\n";
}

/*******************************************************************\

Function: statisticst::html_report_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::html_report_function(std::ostream &out) const
{
  out << "<p class=\"function_statistics\">\n";

  for(time_mapt::const_iterator
      it=time_map.begin(); it!=time_map.end(); it++)
  {
    if(it!=time_map.begin()) out << " ";
    out << html_escape(it->first) << ":&nbsp;"
        << it->second.function
        << "s";
  }
  
  out << "\n</p>\n";
}

/*******************************************************************\

Function: statisticst::next_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::next_function()
{
  functions_processed++;
}

