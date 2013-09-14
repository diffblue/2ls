/*******************************************************************\

Module: Show the overview for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cmath>
#include <fstream>

#include "../html/html_escape.h"
#include "../html/logo.h"

#include "revisions_report.h"
#include "job_status.h"
#include "deltagit_config.h"
#include "log_scale.h"

const char revisions_report_header[]=
#include "revisions_report_header.inc"
;

/*******************************************************************\

Function: htmlize_message

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string htmlize_message(const std::string &src)
{
  std::string result;
  
  result.reserve(src.size());
  
  for(unsigned i=0; i<src.size(); i++)
    switch(src[i])
    {
    case '<': result+="&lt;"; break;
    case '>': result+="&gt;"; break;
    case '"': result+="&quot;"; break;
    case '\'': result+="&apos;"; break;
    case '&': result+="&amp;"; break;
    case '\n': result+="<br>"; break;
    default:
      if(src[i]>=' ') result+=src[i];
    }
  
  return result;
}

/*******************************************************************\

Function: height

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned height(const job_statust &job_status)
{
  unsigned lines=job_status.added+job_status.deleted;
  if(lines==0) return 0;
  if(lines==1) return 1;
  return log10(lines)*10;
}

/*******************************************************************\

Function: revisions_report

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void revisions_report()
{
  deltagit_configt deltagit_config;
  
  std::string title="DeltaCheck Summary of Revisions";
  if(deltagit_config.description!="")
    title+=" "+deltagit_config.description;
  
  std::list<job_statust> jobs;

  get_jobs(jobs);
  
  unsigned max_height=44; // the hight of log_scale.png
  
  std::ofstream out("index.html");
  
  out << "<html>\n"
         "<head>\n";
        
  out << "<title>" << html_escape(title) << "</title>\n";

  out << revisions_report_header;
  
  out << "</head>\n\n";
  
  out << "<body>\n\n";
  
  out << "<img src=\"" << deltacheck_logo
      << "\" class=\"logo\" alt=\"DeltaCheck Logo\">\n\n";
      
  out << "<div class=\"description\">"
      << html_escape(deltagit_config.description)
      << "</div>\n";

  out << "<div class=\"revisions\">\n";
  
  out << "<table>\n"
      << "<tr><td valign=top>\n"
      << "<img src=\"" << log_scale << "\">\n"
      << "</td>\n<td>\n";
  
  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++)
  {
    std::string tooltip=
      "<center>"+j_it->id+"</center>"+
      "<font size=2>";
    if(j_it->author!="") tooltip+="Author: "+html_escape(j_it->author)+"<br>";
    if(j_it->date!="") tooltip+="Date: "+html_escape(j_it->date)+"<br>";
    tooltip+=htmlize_message(j_it->message);
    if(j_it->status!=job_statust::DONE)
      tooltip+="<br><i>"+html_escape(as_string(j_it->status))+"</i>";
    tooltip+=
      "</font>";
      
    unsigned h=std::min(height(*j_it), max_height);
      
    out << "<div class=\"revision\""
           " id=\"rev-" << j_it->id << "\""
           " onMouseOver=\"tooltip.show('" << tooltip << "');\""
           " onMouseOut=\"tooltip.hide();\""
           ">";
    out << "<div "
           " style=\"height: " << h << "px;"
           " background-color: #7070e0;"
           " margin-top: " << max_height-h << "px;\""
           ">";
    out << "</div>";
    out << "</div>";
    out << "\n";
  }
  
  out << "</td></tr></table>\n";
  
  out << "</div>\n";
  
  out << "</body>\n";
  out << "</html>\n";
}
