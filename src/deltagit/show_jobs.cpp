/*******************************************************************\

Module: Show the jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include <util/tempfile.h>
#include <util/prefix.h>

#include "show_jobs.h"

/*******************************************************************\

Function: get_extension

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_extension(const std::string &s)
{
  std::size_t pos=s.rfind('.');
  if(pos==std::string::npos) return "";
  return s.substr(pos+1, std::string::npos);
}

/*******************************************************************\

Function: get_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_file(const std::string &s)
{
  std::size_t pos=s.rfind('/');
  if(pos==std::string::npos) return s;
  return s.substr(pos+1, std::string::npos);
}

/*******************************************************************\

Function: show_jobs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_jobs(std::ostream &out)
{
  temporary_filet tmpfile("deltagit", "log");

  // get the git log
  std::string command;
  command="git log --name-only > "+tmpfile();
  system(command.c_str());

  // rummage through it, looking for 'interesting' commits
  
  std::ifstream in(tmpfile().c_str());
  if(!in) return;
  
  std::string line;
  std::string commit, last_commit;
  std::string svn_id;
  
  while(std::getline(in, line))
  {
    if(has_prefix(line, "commit "))
    {
      commit=line.substr(7, std::string::npos);
    }
    else if(has_prefix(line, "Author: "))
    {
    }
    else if(has_prefix(line, "Date: "))
    {
    }
    else if(has_prefix(line, "    git-svn-id: "))
    {
      std::size_t pos1=line.rfind('@');
      std::size_t pos2=line.rfind(' ');
      if(pos1!=std::string::npos && pos2!=std::string::npos)
        svn_id=line.substr(pos1+1, pos2-pos1-1);
    }
    else if(!line.empty() && line[0]!=' ')
    {
      // shall be file name
      std::string file=get_file(line);
      std::string ext=get_extension(file);
      if(ext=="c" || ext=="C" ||
         ext=="cpp" || ext=="c++" ||
         ext=="h" || ext=="hpp")
      {
        if(commit!=last_commit)
        {
          last_commit=commit;
          out << commit;
          if(svn_id!="") out << " r" << svn_id;
          out << "\n";
        }
      }    
    }
  }
}
