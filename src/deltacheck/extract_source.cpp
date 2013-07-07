/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <cctype>
#include <cstring>
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

// may wish to try http://www.gnu.org/software/src-highlite/

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
{ 
  "auto", "_Bool", "break", "case", "char", "_Complex", "const", "continue",
  "default", "do", "double", "else", "enum", "extern", "float", "for",
  "goto", "if", "inline", "int", "long", "register", "restrict", "return",
  "short", "signed", "sizeof", "static", "struct", "switch", "typedef",
  "union", "unsigned", "void", "volatile", "while", "__float128",
  "__int128", "__int8", "__int16", "__int32", "__int64", "__ptr32",
  "__ptr64", "__complex__", "__complex", "__real__" , "__real", "__imag__" ,
  "__imag", "offsetof", "__asm", "asm", "__asm__", "bool", "catch", "class",
  "constexpr", "delete", "decltype", "explicit", "friend", "mutable",
  "namespace", "new", "nullptr", "operator", "private", "protected",
  "public", "static_assert", "template", "this", "thread_local", "throw",
  "typeid", "typename", "using", "virtual", "wchar_t", "typeof", NULL
};

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
  "!=", "<=", ">=", "::", "->", "##", ".*", "->*", NULL };
  
class tokenizert
{
public:
  explicit tokenizert(const std::string &_buf):buf(_buf)
  {
  }
  
  std::string get();
  std::string peek();
  std::string buf;
};

std::string tokenizert::peek()
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
  
  return buf.substr(0, pos);
}

std::string tokenizert::get()
{
  std::string result=peek();
  buf.erase(0, result.size());
  return result;
}

/*******************************************************************\

Function: html_formattert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class html_formattert
{
public:
  explicit html_formattert(std::ostream &_out):
    different(false), out(_out), comment(false) { }
    
  bool different;
    
  void operator()(const std::string &line);

protected:
  std::ostream &out;
  bool comment;
};

void html_formattert::operator()(const std::string &line)
{
  tokenizert tokenizer(line);
  std::string token;
  
  while(true)
  {
    token=tokenizer.peek();
    if(token==" ") out << tokenizer.get(); else break;
  }

  // open tags  
  if(different) out << "<strong class=\"different\">";
  if(comment) out << "<cite>";
  
  while(!(token=tokenizer.get()).empty())
  {
    if(comment)
    {
      out << html_escape(token);
      if(token=="*/")
      {
        out << "</cite>";
        comment=false;
      }
    }
    else
    {
      if(isalnum(token[0]))
      {
        if(is_keyword(token))
          out << "<em>" << token << "</em>";
        else
          out << "<var>" << token << "</var>";
      }
      else if(token=="/*")
      {
        comment=true;
        out << "<cite>" << token;
      }
      else if(token=="//")
      {
        out << "<cite>" << token;
        while(!(token=tokenizer.get()).empty())
          out << html_escape(token);
        out << "</cite>";
      }
      else if(token[0]=='"' || token[0]=='\'')
      {
        out << "<kbd>" << html_escape(token) << "</kbd>";
      }
      else
        out << html_escape(token);
    }
  }

  // close tags  
  if(comment) out << "</cite>";
  if(different) out << "</strong>";
  
  out << "\n";
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
  const locationt &location,
  const goto_programt &goto_program,
  std::list<linet> &dest)
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
  const locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &out)
{
  std::list<linet> lines;
  get_source(location, goto_program, lines);
  
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
      out << "<div title=\"header=[First row] body=[second row]\" "
             "STYLE=\"BORDER: #558844 1px solid; WIDTH:200px; HEIGHT: 40px\">"
          << "<font color=\"#CC0000\">&#x2717;</font>"
          << "</div>";
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
  
  html_formattert html_formatter(out);
  
  for(std::list<linet>::const_iterator
      l_it=lines.begin(); l_it!=lines.end(); l_it++)
    html_formatter(l_it->line);
  
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
  const locationt &location_old,
  const goto_programt &goto_program_old,
  const locationt &location,
  const goto_programt &goto_program,
  const propertiest &properties,
  std::ostream &out)
{
  // get sources
  std::list<linet> lines, lines_old;

  get_source(location, goto_program, lines);
  get_source(location_old, goto_program_old, lines_old);

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
    html_formattert html_formatter(out);
    
    for(l_old_it=lines_old.begin(), l_it=lines.begin();
        l_old_it!=lines_old.end() && l_it!=lines.end();
        l_old_it++, l_it++)
    {
      html_formatter.different=(l_old_it->line!=l_it->line);
      html_formatter(l_old_it->line);
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
    html_formattert html_formatter(out);
  
    for(l_old_it=lines_old.begin(), l_it=lines.begin();
        l_old_it!=lines_old.end() && l_it!=lines.end();
        l_old_it++, l_it++)
    {
      html_formatter.different=(l_old_it->line!=l_it->line);
      html_formatter(l_it->line);
    }
  }
  
  out << "</pre></td></tr>\n";
  
  out << "</table>\n";
  out << "</p>\n";  
}

