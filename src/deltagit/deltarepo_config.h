/*******************************************************************\

Module: Read Configuration File

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>
#include <list>

enum repo_kindt { NONE, GIT, SVN };

class deltarepo_configt
{
public:
  deltarepo_configt();
  
  std::string url;
  repo_kindt kind;
  std::string last_revision;
  
  typedef std::list<std::string> revisionst;
  revisionst revisions;
  
  void save();
  
  static std::string file_name()
  {
    return "deltarepo.xml";
  }
};
