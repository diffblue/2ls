/*******************************************************************\

Module: 

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

std::string make_relative_path(
  const std::string &directory,
  const std::string &src);

std::string get_directory(const std::string &src);

std::string get_file_name(const std::string &src);

