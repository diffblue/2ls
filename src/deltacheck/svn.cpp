/*******************************************************************\

Module: Delta Check an SVN Repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "svn.h"

class svnt:public messaget
{
public:
  svnt(const std::string &_url,
       const std::string &_revision,
       message_handlert &_message_handler):
    messaget(_message_handler),
    url(_url), revision(_revision)
  {
    doit();
  }
  
protected:
  const std::string &url, &revision;
  
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
  
  void doit();
};

/*******************************************************************\

Function: svnt::get_revisions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void svnt::get_revisions()
{
}

/*******************************************************************\

Function: svnt::doit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void svnt::doit()
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
  svnt(url, revision, message_handler);
}
