/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <cctype>
#include <cstring>
#include <cstdlib>
#include <limits>
#include <fstream>

#ifdef DEBUG
#include <iostream>
#endif

#if defined(__linux__) || defined(__FreeBSD_kernel__) || defined(__CYGWIN__) || defined(__MACH__)
#include <unistd.h>
#endif

#include <util/i2string.h>
#include <util/string2int.h>
#include <util/tempfile.h>

#include "extract_source.h"
#include "html_escape.h"
#include "syntax_highlighting.h"

/*******************************************************************\

Function: fast_forward

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fast_forward(unsigned lines, std::istream &in)
{
  for(unsigned int i=0; i<lines; ++i)
    in.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
}

/*******************************************************************\

Function: get_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct linet
{
  explicit linet():line_no(0) { }
  linet(const irep_idt &_file, unsigned _line_no, const std::string &_line):
    file(_file), line_no(_line_no), line(_line) { }
  irep_idt file;
  unsigned line_no;
  std::string line;
};

void get_source(
  const std::string &path_prefix,
  const locationt &location,
  const goto_programt &goto_program,
  std::list<linet> &dest,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  const irep_idt &file=location.get_file();

  if(file=="") return;
  if(goto_program.instructions.empty()) return;
  
  std::string full_path;

  #ifdef _WIN32
  if((file.size()>=2 && file[1]==':') || file[0]=='\\')
  #else
  if(file[0]=='/')
  #endif
    full_path=id2string(file);
  else
    full_path=path_prefix+id2string(file);

  std::ifstream in(full_path.c_str());
  
  if(!in)
  {
    message.error() << "failed to open source `"
                    << full_path << "'" << messaget::eom;
    dest.push_back(linet(file, 1, "/* failed to open source file */"));
    return;
  }
  
  unsigned first_line=safe_string2unsigned(id2string(location.get_line()));

  if(first_line!=0)
    fast_forward(first_line-1, in);

  // get last line of function
  
  const locationt &last=goto_program.instructions.back().location;
  
  if(last.get_file()!=file)
  {
    // Hm, function ends in a different file than it starts.
    // Possible, but unusual.
    return;
  }

  unsigned end_line=safe_string2unsigned(id2string(last.get_line()));

  for(unsigned line_no=first_line; line_no<=end_line; line_no++)
  {
    std::string s;
    if(!std::getline(in, s)) break;
    dest.push_back(linet(file, line_no, s));
  }
  
}

/*******************************************************************\

Function: get_errors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_errors(
  const propertiest &properties,
  const linet &line)
{
  std::string errors;

  for(propertiest::const_iterator
      p_it=properties.begin(); p_it!=properties.end(); p_it++)
  {
    if(line.file==p_it->loc->location.get_file() &&
       i2string(line.line_no)==as_string(p_it->loc->location.get_line()))
    {
      if(p_it->status.is_false())
      {
        if(!errors.empty()) errors+="<br>";

        irep_idt property=p_it->loc->location.get_property();
        irep_idt comment=p_it->loc->location.get_comment();

        if(comment=="")
          errors+=as_string(property);
        else
          errors+=as_string(comment);
      }
    }
  }
  
  return errors;
}

/*******************************************************************\

Function: extract_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void extract_source(
  const std::string &path_prefix,
  const locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &out,
  message_handlert &message_handler)
{
  std::list<linet> lines;
  get_source(path_prefix, location, goto_program, lines, message_handler);
  
  out << "<p>\n";
  out << "<table class=\"source\"><tr>\n";
  
  // error marking  

  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::list<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
  {
    std::string errors=get_errors(properties, *l_it);
    if(!errors.empty())
    {
      out << "<span style=\"color:#CC0000\" onmouseover=\"tooltip.show('"
          << html_escape(errors) << "');\""
                 " onmouseout=\"tooltip.hide();\">"
          << "&#x2717;"
          << "</span>";
    }
    out << "\n";
  }
    
  out << "</pre></td>\n";

  // line numbers go into a column
  
  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::list<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
    out << l_it->line_no << "\n";
    
  out << "</pre></td>\n";
  
  // now do source text in another column
  
  out << "<td class=\"code\"><pre>\n";
  
  syntax_highlightingt syntax_highlighting(out);
  
  for(std::list<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
  {
    syntax_highlighting.line_no=l_it->line_no;
    syntax_highlighting(l_it->line);
  }
  
  out << "</pre></td></tr>\n";
  
  out << "</table>\n";
  out << "</p>\n";
}

/*******************************************************************\

Function: diff_action

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class diff_actiont
{
public:
  char action;
  unsigned old_from, old_to, old_size;
  unsigned new_from, new_to, new_size;
  diff_actiont(const std::string &);

  void output(std::ostream &out)
  {
    if(action!=0)
      out << "Action: " << action
          << " Old: " << old_from << "-" << old_to << " (" << old_size << ")"
          << " New: " << new_from << "-" << new_to << " (" << new_size << ")"
          << "\n";
  }
};

diff_actiont::diff_actiont(const std::string &src)
{
  old_from=old_to=new_from=new_to=old_size=new_size=0;
  action=0;

  // e.g. 4,5c4
  if(src.empty() || !isdigit(src[0])) return;
  
  std::string old_from_str, old_to_str, new_from_str, new_to_str;

  unsigned i;

  for(i=0; i<src.size() && isdigit(src[i]); i++) old_from_str+=src[i];

  if(i<src.size() && src[i]==',')
    for(i++; i<src.size() && isdigit(src[i]); i++) old_to_str+=src[i];
  else
    old_to_str=old_from_str;
    
  if(i<src.size() && isalpha(src[i]))
    action=src[i];
  else
    return;

  for(i++; i<src.size() && isdigit(src[i]); i++) new_from_str+=src[i];

  if(i<src.size() && src[i]==',')
    for(i++; i<src.size() && isdigit(src[i]); i++) new_to_str+=src[i];
  else
    new_to_str=new_from_str;

  old_from=atoi(old_from_str.c_str());
  old_to=atoi(old_to_str.c_str());
  new_from=atoi(new_from_str.c_str());
  new_to=atoi(new_to_str.c_str());
  
  old_size=old_to-old_from+1;
  new_size=new_to-new_from+1;
  
  if(action=='a')
    old_size=0;
  else if(action=='d')
    new_size=0;

  // sanity check
  if(old_from>old_to || new_from>new_to) action=0;
}
  
/*******************************************************************\

Function: process_diff

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void process_diff(
  std::list<linet> &lines1,
  std::list<linet> &lines2,
  const std::list<std::string> &diff)
{
  std::vector<std::list<linet>::iterator> l_it1, l_it2;
  
  for(std::list<linet>::iterator it=lines1.begin();
      it!=lines1.end(); it++)
    l_it1.push_back(it);

  for(std::list<linet>::iterator it=lines2.begin();
      it!=lines2.end(); it++)
    l_it2.push_back(it);

  for(std::list<std::string>::const_iterator
      d_it=diff.begin();
      d_it!=diff.end();
      d_it++)
  {
    diff_actiont da(*d_it);
    
    #ifdef DEBUG
    da.output(std::cout);
    #endif

    switch(da.action)
    {
    case 'c': // change
      if(da.new_size>da.old_size)
      {
        for(unsigned i=da.old_size; i<da.new_size; i++)
          lines1.insert(l_it1[da.old_from], linet());
      }
      else if(da.old_size>da.new_size)
      {
        for(unsigned i=da.new_size; i<da.old_size; i++)
          lines2.insert(l_it2[da.old_from], linet());
      }
      break;
      
    case 'a': // add
      for(unsigned i=0; i<da.new_size; i++)
        lines1.insert(l_it1[da.old_from], linet());
      break;

    case 'd': // delete
      for(unsigned i=0; i<da.old_size; i++)
        lines2.insert(l_it2[da.old_from], linet());
      break;
    }
  }
}

/*******************************************************************\

Function: diff_it

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void diff_it(
  std::list<linet> &lines1,
  std::list<linet> &lines2)
{
  std::string tmp1_name=get_temporary_file("delta_diff1", "txt");
  std::string tmp2_name=get_temporary_file("delta_diff2", "txt");
  std::string tmp3_name=get_temporary_file("delta_diff3", "txt");

  {  
    std::ofstream out1(tmp1_name.c_str());
    std::ofstream out2(tmp2_name.c_str());
    
    for(std::list<linet>::const_iterator l_it=lines1.begin();
        l_it!=lines1.end(); l_it++)
      out1 << l_it->line << "\n";

    for(std::list<linet>::const_iterator l_it=lines2.begin();
        l_it!=lines2.end(); l_it++)
      out2 << l_it->line << "\n";
  }
  
  std::string cmdline="diff \""+tmp1_name+"\""+
                          " \""+tmp2_name+"\""+
                         "> \""+tmp3_name+"\"";
  
  system(cmdline.c_str());

  // open output
  {
    std::ifstream in(tmp3_name.c_str());
    std::string line;
    std::list<std::string> diff;
    while(std::getline(in, line)) diff.push_back(line);
    process_diff(lines1, lines2, diff);
  }
  
  // clean up
  unlink(tmp1_name.c_str());
  unlink(tmp2_name.c_str());
  unlink(tmp3_name.c_str());
}

/*******************************************************************\

Function: extract_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void extract_source(
  const std::string &path_prefix_old,
  const locationt &location_old,
  const goto_programt &goto_program_old,
  const std::string &path_prefix,
  const locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &out,
  message_handlert &message_handler)
{
  // get sources
  std::list<linet> lines, lines_old;

  get_source(path_prefix_old, location, goto_program, lines, message_handler);
  get_source(path_prefix, location_old, goto_program_old, lines_old, message_handler);

  // run 'diff'
  
  diff_it(lines_old, lines);
  
  out << "<p>\n";
  out << "<table class=\"source\">\n";  
  out << "<tr><th colspan=2>old version</th>"
         "<th colspan=3>new version</th></tr>\n";
  
  out << "<tr>\n";
  
  // old version

 std::list<linet>::const_iterator l_old_it, l_it;
 
  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::list<linet>::const_iterator
      l_old_it=lines_old.begin(); l_old_it!=lines_old.end(); l_old_it++)
  {
    if(l_old_it->line_no!=0) out << l_old_it->line_no;
    out << "\n";
  }
    
  out << "</pre></td>\n";
  
  out << "<td class=\"code\"><pre>\n";

  {  
    syntax_highlightingt syntax_highlighting(out);
    
    for(l_old_it=lines_old.begin(), l_it=lines.begin();
        l_old_it!=lines_old.end() && l_it!=lines.end();
        l_old_it++, l_it++)
    {
      syntax_highlighting.different=(l_old_it->line!=l_it->line);
      syntax_highlighting.line_no=l_it->line_no;
      syntax_highlighting.id_suffix="_old";
      syntax_highlighting(l_old_it->line);
    }
  }
  
  out << "</pre></td>\n";
  
  // new version
  
  // error marking  
  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::list<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
  {
    std::string errors=get_errors(properties, *l_it);
    if(!errors.empty())
    {
      out << "<span style=\"color:#CC0000\" onmouseover=\"tooltip.show('"
          << html_escape(errors) << "');\""
                 " onmouseout=\"tooltip.hide();\">"
          << "&#x2717;"
          << "</span>";
    }
    out << "\n";
  }
    
  out << "</pre></td>\n";

  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::list<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
  {
    if(l_it->line_no!=0) out << l_it->line_no;
    out << "\n";
  }
    
  out << "</pre></td>\n";

  
  out << "<td class=\"code\"><pre>\n";
  
  {
    syntax_highlightingt syntax_highlighting(out);
  
    for(l_old_it=lines_old.begin(), l_it=lines.begin();
        l_old_it!=lines_old.end() && l_it!=lines.end();
        l_old_it++, l_it++)
    {
      syntax_highlighting.different=(l_old_it->line!=l_it->line);
      syntax_highlighting.line_no=l_it->line_no;
      syntax_highlighting(l_it->line);
    }
  }
  
  out << "</pre></td></tr>\n";
  
  out << "</table>\n";
  out << "</p>\n";  
}

