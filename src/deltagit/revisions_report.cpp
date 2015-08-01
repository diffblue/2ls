/*******************************************************************\

Module: Show the overview for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cmath>
#include <fstream>

#include <util/string2int.h>
#include <json/json_parser.h>

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

Function: shorten_message

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string shorten_message(const std::string &src)
{
  std::string result;
  
  result.reserve(src.size());
  
  unsigned line_count=1;
  
  for(unsigned i=0; i<src.size(); i++)
  {
    result+=src[i];

    if(src[i]=='\n')
    {
      line_count++;
    
      if(line_count>20) // arbitrary magic number
      {
        result+="...\n";
        break;
      }
    }
  }
  
  return result;
}

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
    case '&': result+="&amp;"; break;
    case '\n': result+="<br>"; break;

    // &apos; does not seem to be universally supported,
    // and Unicode seems to suggest to prefer &#8217; over &#39;
    case '\'': result+="&8217;"; break;
            
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

void revisions_report(
  bool partial_html,
  const std::string &rel_path,
  unsigned max_revs)
{
  deltagit_configt deltagit_config;
  
  std::string title="DeltaCheck Summary of Revisions";
  if(deltagit_config.description!="")
    title+=" "+deltagit_config.description;
  
  std::list<job_statust> jobs;

  get_jobs(jobs);
  
  unsigned max_height=44; // the hight of log_scale.png
  
  std::string outfile_name=
    partial_html?"include.html":"index.html";
  
  std::ofstream out(outfile_name.c_str());

  if(!partial_html)
  { 
    out << "<!DOCTYPE html>\n"; 
    out << "<html>\n"
           "<head>\n"
           "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\">\n";
        
    out << "<title>" << html_escape(title) << "</title>\n";

    out << revisions_report_header;
  
    out << "</head>\n\n";
  
    out << "<body>\n\n";
  
    out << "<img src=\"" << deltacheck_logo
        << "\" class=\"logo\" alt=\"DeltaCheck Logo\">\n\n";
  }

  out << "<div class=\"description\">"
      << html_escape(deltagit_config.description)
      << "</div>\n";

  out << "<div class=\"revisions\">\n";
  
  out << "<table>\n"
      << "<tr><td valign=top>\n"
      << "<img src=\"" << "log_scale.png" << "\">\n"
      << "</td>\n<td>\n";
      
  unsigned counter=0, number_of_jobs=jobs.size();
  
  for(std::list<job_statust>::const_iterator
      j_it=jobs.begin();
      j_it!=jobs.end();
      j_it++, counter++)
  {
    if(max_revs!=0 &&
       counter+max_revs<number_of_jobs)
      continue; // skip
  
    // read deltacheck summary, if available
    unsigned passed=0, failed=0;

    {    
      std::string summary_file_name=j_it->get_wd()+"/deltacheck-stat.json";
      jsont deltacheck_summary;
      null_message_handlert null_message_handler;
      parse_json(summary_file_name, null_message_handler, deltacheck_summary);
      const jsont &properties=deltacheck_summary["properties"];
      passed=unsafe_string2unsigned(properties["passed"].value);
      failed=unsafe_string2unsigned(properties["failed"].value);
    }
  
    std::string tooltip=
      "<center>"+j_it->id+"</center>"+
      "<font size=2>";
    if(j_it->author!="") tooltip+="Author: "+html_escape(j_it->author)+"<br>";
    if(j_it->date!="") tooltip+="Date: "+html_escape(j_it->date)+"<br>";
    tooltip+=htmlize_message(shorten_message(j_it->message));
    if(j_it->stage!=job_statust::DONE)
    {
      tooltip+="<br><i>"+html_escape(as_string(j_it->stage));
      tooltip+=" "+html_escape(as_string(j_it->status));
      if(j_it->hostname!="" && j_it->status!=job_statust::WAITING)
        tooltip+=" on "+html_escape(as_string(j_it->hostname));
      tooltip+="</i>";
    }
    tooltip+=
      "</font>";
      
    unsigned h=std::min(height(*j_it), max_height);

    std::string link;
    std::string bar_color="#7070e0";
    
    if(j_it->stage==job_statust::ANALYSE)
    {
      link=rel_path+"/"+j_it->get_wd()+"/deltacheck-diff.html";
    }
    else if(j_it->stage==job_statust::DONE)
    {
      link=rel_path+"/"+j_it->get_wd()+"/deltacheck-diff.html";

      unsigned r, g;
      if(passed+failed==0)
      {
        r=0;
        g=255;
      }
      else
      {
        r=(unsigned long long)255*failed/(passed+failed);
        g=(unsigned long long)255*passed/(passed+failed);
      }

      char buffer[100];
      snprintf(buffer, 100, "#%02x%02x30", r, g);
      bar_color=buffer;
    }
    else
    {
      if(j_it->status==job_statust::FAILURE)
        bar_color="#e0e0e0";
    }
    
    if(link!="")
      out << "<a href=\"" << html_escape(link) << "\">";
    
    out << "<div class=\"revision\""
           " id=\"rev-" << j_it->id << "\""
           " onMouseOver=\"tooltip.show('" << tooltip << "');\""
           " onMouseOut=\"tooltip.hide();\""
           ">";

    out << "<div "
           " style=\"height: " << h << "px;"
           " background-color: " << bar_color << ";"
           " margin-top: " << max_height-h << "px;\""
           ">";

    out << "</div>";
    out << "</div>";
    
    if(link!="")
      out << "</a>";

    out << "\n";
  }
  
  out << "</td></tr></table>\n";
  
  // revisions
  out << "</div>\n";
  
  if(!partial_html)
  {
    out << "</body>\n";
    out << "</html>\n";
  }
}
