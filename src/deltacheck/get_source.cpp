/*******************************************************************\

Module: Get Source Code

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>
#include <limits>

#include <unistd.h>

#include <util/string2int.h>

#include "../functions/path_util.h"
#include "get_source.h"

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

void get_source(
  const std::string &path_prefix,
  const source_locationt &location,
  const goto_programt &goto_program,
  std::list<linet> &dest,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  const irep_idt &file=location.get_file();

  if(file=="") return;
  if(goto_program.instructions.empty()) return;

  // split up path_prefix into directories  
  std::list<std::string> directories;
  
  {
    std::string tmp;
    for(unsigned i=0; i<path_prefix.size(); i++)
    {
      if(path_prefix[i]=='/' && !tmp.empty())
      {
        directories.push_back(tmp);
        tmp.clear();
      }
      
      tmp+=path_prefix[i];
    }
    
    if(!tmp.empty() && tmp!="/") directories.push_back(tmp);
  }
  
  // try prefixes of path_prefix
  
  std::string full_path;
  
  for(int i=directories.size(); i>=0; i--)
  {
    std::string prefix;
    for(std::list<std::string>::const_iterator
        p_it=directories.begin();
        p_it!=directories.end();
        p_it++)
      prefix+=*p_it;
  
    full_path=
      make_relative_path(prefix, id2string(file));
    
    if(access(full_path.c_str(), R_OK)==0) break; // found!
  }

  std::ifstream in;
  in.open(full_path.c_str());

  if(!in)
  {
    message.error() << "failed to open source `"
                    << file << "'" << messaget::eom;
    if(!directories.empty())
      message.error() << "also tried prefixes of `" << path_prefix << "'"
                      << messaget::eom;
    dest.push_back(linet(file, 1, "/* failed to open source file */"));
    dest.push_back(linet(file, 2, "/* "+full_path+" */"));
    return;
  }
  
  unsigned first_line=safe_string2unsigned(id2string(location.get_line()));

  if(first_line!=0)
    fast_forward(first_line-1, in);

  // get last line of function
  
  const source_locationt &last=goto_program.instructions.back().source_location;
  
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
