/*******************************************************************\

Module: Read Configuration File

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

enum repo_kindt { NONE, GIT, SVN };

class deltarepo_configt
{
public:
  deltarepo_configt();
  
  std::string url;
  repo_kindt kind;
  
  void save();
  
  static std::string file_name()
  {
    return "deltarepo.xml";
  }
};
