/*******************************************************************\

Module: Get git log as data structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTAGIT_GIT_LOG_H
#define DELTAGIT_GIT_LOG_H

#include <string>
#include <list>

class git_logt
{
public:
  class entryt
  {
  public:
    std::string commit;
    std::string author;
    std::string date;
    std::string git_svn_id;
    std::list<std::string> files;
  };
  
  typedef std::list<entryt> entriest;
  entriest entries;

  // Read at most max_commits many entries;
  // 0 means no limit.
  explicit git_logt(unsigned max_commits=0)
  {
    read(max_commits);
  }

protected:
  void read(unsigned max_commits);
};

#endif
