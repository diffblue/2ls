/*******************************************************************\

Module: Extract Source Code

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GET_SOURCE_H
#define CPROVER_GET_SOURCE_H

#include <string>
#include <list>

#include <util/message.h>
#include <goto-programs/goto_program.h>

struct linet
{
  explicit linet():line_no(0) { }
  linet(const irep_idt &_file, unsigned _line_no, const std::string &_line):
    file(_file), line_no(_line_no), line(_line) { }
  irep_idt file;
  unsigned line_no;
  std::string line;
};

void get_source(
  const std::string &path_prefix,
  const source_locationt &location,
  const goto_programt &goto_program,
  std::list<linet> &dest,
  message_handlert &message_handler);

#endif
