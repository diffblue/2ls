/*******************************************************************\

Module: Data

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_DATA_H
#define CPROVER_DELTACHECK_DATA_H

#include <util/irep.h>

class entryt
{
public:
  irep_idt file;
  unsigned line;
  irep_idt category;
  std::string message;
};

class datat
{
public:
  typedef std::vector<entryt> entriest;
  entriest entries;
  
  std::string description;

  inline void add(const entryt &e)
  {
    entries.push_back(e);
  }
  
  void read(const std::string &file);
  void read(const class xmlt &);
};

#endif
