/*******************************************************************\

Module: Deltagit configuration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTAGIT_CONFIG_H
#define DELTAGIT_CONFIG_H

#include <string>

class deltagit_configt
{
public:
  deltagit_configt()
  {
    read();
  }

  std::string description;

  void read();
  
protected:
};

#endif
