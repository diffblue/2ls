/*******************************************************************\

Module: Extract Source for HTML

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

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
  const irep_idt &file=location.get_file();

  if(file=="") return;
  if(goto_program.instructions.empty()) return;

  std::ifstream in(file.c_str());
  
  if(!in)
  {
    out << "<p>failed to open \""
        << html_escape(file) << "\"</p>\n";
    return;
  }
  
  unsigned line_no=safe_string2unsigned(id2string(location.get_line()));

  if(line_no!=0)
    fast_forward(line_no-1, in);

  // get last line of function
  
  const locationt &last=goto_program.instructions.back().location;
  
  if(last.get_file()!=file)
  {
    // Hm, function ends in a different file than it starts.
    // Possible, but unusual.
    return;
  }

  unsigned end_line=safe_string2unsigned(id2string(last.get_line()));
  
  out << "<table class=\"source\"><tr>\n";
  
  // line numbers go into a column
  
  out << "<td class=\"line_numbers\">\n";
  
  for(; line_no<=end_line; line_no++)
    out << line_no << "<br>";
    
  out << "</td>\n";
  
  // now do source text in another column
  
  out << "<td class=\"code\"><pre>\n";
  
  for(; line_no<=end_line; line_no++)
  {
    std::string line;
    if(!std::getline(in, line)) break;
    out << line << "\n";
  }
  
  out << "</pre></td>\n";
  
  out << "</table>\n";
}
