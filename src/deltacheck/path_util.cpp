/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

/*******************************************************************\

Function: make_relative_path

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string make_relative_path(
  const std::string &directory,
  const std::string &src)
{
  // is src already absolute?
  
  #ifdef _WIN32
  if((src.size()>=2 && src[1]==':') || src[0]=='\\')
    return src;
  #else
  if(src[0]=='/')
    return src;
  #endif

  // anything given?  
  if(directory.empty()) return src;
  
  // otherwise, stitch together
  #ifdef _WIN32
  const char pathsep='\\';
  #else
  const char pathsep='/';
  #endif
  
  if(directory[directory.size()-1]==pathsep)
    return directory+src;
  else
    return directory+std::string(1, pathsep)+src;
}

/*******************************************************************\

Function: make_relative_path

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_directory(const std::string &src)
{
  #ifdef _WIN32
  const char pathsep='\\';
  #else
  const char pathsep='/';
  #endif
  
  std::size_t last_pos=src.rfind(pathsep);
  
  if(last_pos==std::string::npos)
    return ""; // no directory given

  // cut off file name
  return std::string(src, 0, last_pos);
}

