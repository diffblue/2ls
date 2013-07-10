/*******************************************************************\

Module: Delta Check an SVN Repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "versioning.h"

class versioningt:public messaget
{
public:
  explicit versioningt(message_handlert &_message_handler):
    messaget(_message_handler)
  {
  }
  
  void svn(const std::string &url,
           const std::string &revision);
  
protected:
  void get_revisions();
  
  class revisiont
  {
  public:
    std::string date;
    std::string msg;
    std::string author;
  };
  
  // maps revision_id -> revisiont
  typedef std::map<std::string, revisiont> revision_mapt;
};

/*******************************************************************\

Function: versioningt::get_revisions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void versioningt::get_revisions()
{
}

/*******************************************************************\

Function: versioningt::svn

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void versioningt::svn(
  const std::string &url,
  const std::string &revision)
{
  get_revisions();
}

/*******************************************************************\

Function: svn

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void svn(const std::string &url,
         const std::string &revision,
         message_handlert &message_handler)
{
  versioningt versioning(message_handler);
  versioning.svn(url, revision);
}
