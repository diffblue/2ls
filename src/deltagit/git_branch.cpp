/*******************************************************************\

Module: Get git branch -a as data structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>

#include <util/prefix.h>
#include <util/tempfile.h>

#include "git_branch.h"

/*******************************************************************\

Function: git_brancht::read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void git_brancht::read()
{
  temporary_filet tmpfile("deltagit", "log");

  // get the git branches by running "git branch -a"
  std::string command;
  command="git branch --list -a -v --no-abbrev > "+tmpfile();
  system(command.c_str());

  // read it from temporary file
  
  std::ifstream in(tmpfile().c_str());
  if(!in) return;
  
  std::string line;
  
  
  while(std::getline(in, line))
  {
    if(has_prefix(line, "* ") || has_prefix(line, "  "))
    {
      const std::size_t branch_end=line.find(' ', 2);
      if(branch_end==std::string::npos) continue;

      const std::size_t commit_pos=line.find_first_not_of(' ', commit_pos);
      if(commit_pos==std::string::npos) continue;

      std::size_t commit_end=line.find(' ', commit_pos);
      if(commit_end==std::string::npos) commit_end=line.size();

      entryt entry;
      entry.name=line.substr(2, branch_end-1);
      entry.commit=line.substr(commit_pos, commit_pos-commit_end);
      entries.push_back(entry);
    }
  }
}
