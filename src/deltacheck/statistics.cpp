/*******************************************************************\

Module: Statistics

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "../html/html_escape.h"
#include "statistics.h"

/*******************************************************************\

Function: statisticst::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::clear()
{
  time_map.clear();
  number_map.clear();
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
  t.last=this_period;
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
  
  for(number_mapt::const_iterator
      it=number_map.begin(); it!=number_map.end(); it++)
  {
    out << "<tr><td>";
    out << html_escape(it->first) << ":</td><td>"
        << it->second
        << "</td></tr>\n";
  }
  
  for(time_mapt::const_iterator
      it=time_map.begin(); it!=time_map.end(); it++)
  {
    out << "<tr><td>";
    out << html_escape(it->first) << ":</td><td>"
        << it->second.total
        << "s</td></tr>\n";
  }
  
  out << "</table>\n";
  
  out << "</p>\n";
}

/*******************************************************************\

Function: statisticst::html_report_last

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void statisticst::html_report_last(std::ostream &out) const
{
  out << "<p class=\"function_statistics\">\n";

  for(time_mapt::const_iterator
      it=time_map.begin(); it!=time_map.end(); it++)
  {
    if(it!=time_map.begin()) out << " ";
    out << html_escape(it->first) << ":&nbsp;"
        << it->second.last
        << "s";
  }
  
  out << "\n</p>\n";
}

