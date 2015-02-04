/*******************************************************************\

Module: Syntax Highlighting

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SYNTAX_HIGHLIGHTING_H
#define CPROVER_SYNTAX_HIGHLIGHTING_H

#include <iosfwd>
#include <string>

class syntax_highlightingt
{
public:
  explicit syntax_highlightingt(std::ostream &_out):
    out(_out), comment(false) { }

  std::string strong_class;    
  unsigned line_no;
  std::string id_suffix;
    
  void operator()(const std::string &line);

protected:
  std::ostream &out;
  bool comment;
};

#endif
