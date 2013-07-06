/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cctype>
#include <cstring>
#include <limits>
#include <fstream>

#include <util/i2string.h>
#include <util/string2int.h>

#include "extract_source.h"
#include "html_escape.h"

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

Function: is_keyword

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *keywords[]=
{ NULL };

bool is_keyword(const std::string &token)
{
  for(unsigned i=0; keywords[i]!=NULL; i++)
  {
    if(strcmp(keywords[i], token.c_str())==0)
      return true;
  }
  
  return false;
}
  
/*******************************************************************\

Function: source_token

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *tokens[]=
{ "++", "+=", "--", "-=", "&&", "&=", "||", "|=", "/*",
  "*/", "//", "%=", "/=", "<<", ">>", "<<=", ">>=", "==",
  "!=", "<=", ">=", "::", "->", "##", NULL };
  
class tokenizert
{
public:
  explicit tokenizert(const std::string &_buf):buf(_buf)
  {
  }
  
  std::string get();
  std::string buf;
};

std::string tokenizert::get()
{
  if(buf.empty()) return buf;

  char first=buf[0];
  
  unsigned pos=1;
  
  if(isalnum(first))
  {
    // identifier or keyword or number
    for(pos=1; pos<buf.size() && isalnum(buf[pos]); pos++);
  }
  else if(first=='"' || first=='\'')
  {
    // string literal or character literal
    while(pos<buf.size())
    {
      if(buf[pos]==first)
        break; // end
      else if(buf[pos]=='\\' && (pos+1)<buf.size()) // escape
        pos+=2;
      else
        pos++;
    }
  }
  else
  {
    for(pos=1; pos<buf.size(); pos++)
    {
      bool match=false;
    
      for(unsigned t=0; tokens[t]!=NULL; t++)
      {
        if(strncmp(tokens[t], buf.c_str(), pos)==0)
        {
          match=true;
          break;
        }
      }

      // no more matches
      if(!match)
      {
        if(pos!=1) pos--;
        break;
      }
    }
  }
  
  std::string result=buf.substr(0, pos);
  buf.erase(0, pos);
  return result;
}

/*******************************************************************\

Function: html_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void html_source(
  const std::string &line,
  std::ostream &out)
{
  tokenizert tokenizer(line);

  std::string token;
  
  while(!(token=tokenizer.get()).empty())
  {
    if(isalnum(token[0]))
    {
      if(is_keyword(token))
        out << "<em>" << token << "</em>";
      else
        out << "<var>" << token << "</var>";
    }
    else if(token[0]=='"' || token[0]=='\'')
    {
      out << "<kbd>" << html_escape(token) << "</kbd>";
    }
    else
      out << html_escape(token);
  }
}

/*******************************************************************\

Function: get_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct linet
{
  linet(unsigned _line_no, std::string &_line):
    line_no(_line_no), line(_line) { }
  unsigned line_no;
  std::string line;
};

void get_source(
  const locationt &location,
  const goto_programt &goto_program,
  std::vector<linet> &dest)
{
  const irep_idt &file=location.get_file();

  if(file=="") return;
  if(goto_program.instructions.empty()) return;

  std::ifstream in(file.c_str());
  
  if(!in) return;
  
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
    dest.push_back(linet(line_no, s));
  }
  
}

/*******************************************************************\

Function: extract_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void extract_source(
  const locationt &location,
  const goto_programt &goto_program,
  std::ostream &out)
{
  std::vector<linet> lines;
  get_source(location, goto_program, lines);
  
  out << "<p>\n";
  out << "<table class=\"source\"><tr>\n";
  
  // line numbers go into a column
  
  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::vector<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
    out << l_it->line_no << "\n";
    
  out << "</pre></td>\n";
  
  // now do source text in another column
  
  out << "<td class=\"code\"><pre>\n";
  
  for(std::vector<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
  {
    html_source(l_it->line, out);
    out << "\n";
  }
  
  out << "</pre></td></tr>\n";
  
  out << "</table>\n";
  out << "</p>\n";
}

/*******************************************************************\

Function: extract_source

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void extract_source(
  const locationt &location_old,
  const goto_programt &goto_program_old,
  const locationt &location,
  const goto_programt &goto_program,
  std::ostream &out)
{
  std::vector<linet> lines, lines_old;
  get_source(location, goto_program, lines);
  get_source(location_old, goto_program_old, lines_old);
  
  out << "<p>\n";
  out << "<table class=\"source\"><tr>\n";
  
  // old version

  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::vector<linet>::const_iterator
      l_it=lines_old.begin(); l_it!=lines_old.end(); l_it++)
    out << l_it->line_no << "\n";
    
  out << "</pre></td>\n";
  
  out << "<td class=\"code\"><pre>\n";
  
  for(std::vector<linet>::const_iterator
      l_it=lines_old.begin(); l_it!=lines_old.end(); l_it++)
  {
    html_source(l_it->line, out);
    out << "\n";
  }
  
  out << "</pre></td>\n";
  
  // new version
  
  out << "<td class=\"line_numbers\"><pre>\n";
  
  for(std::vector<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
    out << l_it->line_no << "\n";
    
  out << "</pre></td>\n";
  
  out << "<td class=\"code\"><pre>\n";
  
  for(std::vector<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
  {
    html_source(l_it->line, out);
    out << "\n";
  }
  
  out << "</pre></td></tr>\n";
  
  out << "</table>\n";
  out << "</p>\n";  
}

