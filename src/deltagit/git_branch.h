/*******************************************************************\

Module: Get git branch -a as data structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTAGIT_GIT_BRANCH_H
#define DELTAGIT_GIT_BRANCH_H

#include <string>
#include <list>

class git_brancht
{
public:
  class entryt
  {
  public:
    std::string name;
    std::string commit;
  };
  
  typedef std::list<entryt> entriest;
  entriest entries;
  
  git_brancht()
  {
    read();
  }

protected:
  void read();
};

#endif
