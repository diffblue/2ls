/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

#ifdef _WIN32
const char pathsep='\\';
#else
const char pathsep='/';
#endif

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
  if(directory[directory.size()-1]==pathsep)
    return directory+src;
  else
    return directory+std::string(1, pathsep)+src;
}

/*******************************************************************\

Function: get_directory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_directory(const std::string &src)
{
  std::size_t last_pos=src.rfind(pathsep);
  
  if(last_pos==std::string::npos)
    return ""; // no directory given

  // cut off file name, but keep pathsep
  return std::string(src, 0, last_pos+1);
}

/*******************************************************************\

Function: get_file_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string get_file_name(const std::string &src)
{
  std::size_t last_pos=src.rfind(pathsep);
  
  if(last_pos==std::string::npos)
    return src; // no directory given

  // cut off directory
  return std::string(src, last_pos+1, std::string::npos);
}

