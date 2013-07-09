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
  }
  
protected:
  const std::string &url, &revision;
};

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
