/*******************************************************************\

Module: Summarization

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_INDEX_H
#define CPROVER_DELTACHECK_INDEX_H

#include <vector>
#include <string>
#include <set>
#include <ostream>

#include <util/message.h>

void build_index(
  const std::vector<std::string> &files,
  const std::string &description,
  std::ostream &out,
  message_handlert &);

class indext
{
public:
  // function names to file
  typedef std::map<irep_idt, std::set<irep_idt> > function_to_filet;
  function_to_filet function_to_file;
  
  struct filet
  {
    std::set<irep_idt> functions;
  };

  // file names to filet  
  typedef std::map<irep_idt, filet> filest;
  
  typedef std::set<irep_idt> functionst;
  functionst functions;
  
  void read(const std::string &file, message_handlert &);
  
  std::string description, file_name;
};

#endif
