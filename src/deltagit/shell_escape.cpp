/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "shell_escape.h"

/*******************************************************************\

Function: shell_escape

  Inputs:

 Outputs:

 Purpose: escape characters for bash

\*******************************************************************/

std::string shell_escape(const std::string &src)
{
  bool clean=true;
  
  for(std::string::const_iterator
      it=src.begin(); it!=src.end(); it++)
  {
    // positive list of safe characters
    if(isalnum(*it) || *it=='_' || *it=='/' ||
       *it=='.' || *it==':')
    {
    }
    else
      clean=false;
  }
  
  if(clean)
    return src;

  std::string result;
  result.reserve(src.size()+2);
  
  result+='\'';
  
  for(std::string::const_iterator
      it=src.begin(); it!=src.end(); it++)
  {
    if(*it=='\'')
      result+="'\\''"; // quote, backslash, quote
    else
      result+=*it;
  }
  
  result+='\'';
  
  return result;
}
