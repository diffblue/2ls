/*******************************************************************\

Module: Data

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_DATA_H
#define CPROVER_DELTACHECK_DATA_H

#include <util/irep.h>

class datat
{
public:
  class propertyt
  {
  public:
    irep_idt file;
    unsigned line;
    irep_idt category;
    std::string message;
  };

  typedef std::vector<propertyt> propertiest;
  propertiest properties;
  
  std::string description;

  inline void add(const propertyt &e)
  {
    properties.push_back(e);
  }
  
  void read(const std::string &file);
  void read(const class xmlt &);
};

#endif
