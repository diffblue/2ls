/*******************************************************************\

Module: Show the jobs for a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>
#include <fstream>

#include <util/tempfile.h>
#include <util/prefix.h>

#include "show_jobs.h"
#include "git_log.h"

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
  // get the git log
  git_logt git_log;

  // rummage through it, looking for 'interesting' commits
  for(git_logt::entriest::const_iterator
      l_it=git_log.entries.begin();
      l_it!=git_log.entries.end();
      l_it++)
  {
    bool found=false;
  
    for(std::list<std::string>::const_iterator
        f_it=l_it->files.begin();
        f_it!=l_it->files.end();
        f_it++)
    {
      std::string file=get_file(*f_it);
      std::string ext=get_extension(file);

      if(ext=="c" || ext=="C" ||
         ext=="cpp" || ext=="c++" ||
         ext=="h" || ext=="hpp")
      {
        found=true;
        break;
      }    
    }

    if(found)
    {
      out << l_it->commit;
      if(l_it->git_svn_id!="") out << " r" << l_it->git_svn_id;
      out << "\n";
    }
  }
}
