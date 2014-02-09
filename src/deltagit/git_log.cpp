/*******************************************************************\

Module: Get git log as data structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>

#include <util/i2string.h>
#include <util/prefix.h>
#include <util/tempfile.h>

#include "git_log.h"

/*******************************************************************\

Function: git_logt::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void git_logt::read(unsigned max_commits)
{
  temporary_filet tmpfile("deltagit", "log");

  // get the git log by running "git log"
  std::string command;
  command="cd source-repo; git log --name-only";
  if(max_commits!=0) command+="--max-count="+i2string(max_commits);
  command+=" > "+tmpfile();
  system(command.c_str());

  // read it from temporary file
  
  std::ifstream in(tmpfile().c_str());
  if(!in) return;
  
  std::string line;
  
  entryt entry;
  
  while(std::getline(in, line))
  {
    if(has_prefix(line, "commit "))
    {
      if(entry.commit!="")
      {
        entries.push_back(entry);
        entry=entryt(); // clear it
      }

      entry.commit=line.substr(7, std::string::npos);
    }
    else if(has_prefix(line, "Author: "))
    {
      entry.author=line.substr(8, std::string::npos);
    }
    else if(has_prefix(line, "Date:   "))
    {
      entry.date=line.substr(8, std::string::npos);
    }
    else if(has_prefix(line, "    git-svn-id: "))
    {
      std::size_t pos1=line.rfind('@');
      std::size_t pos2=line.rfind(' ');
      if(pos1!=std::string::npos && pos2!=std::string::npos)
        entry.git_svn_id=line.substr(pos1+1, pos2-pos1-1);
    }
    else if(!line.empty() && line[0]!=' ')
    {
      // shall be file name
      entry.files.push_back(line);
    }
  }

  // last one
  if(entry.commit!="")
    entries.push_back(entry);
}
