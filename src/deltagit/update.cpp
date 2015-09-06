/*******************************************************************\

Module: Update a repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "update.h"
#include "deltarepo_config.h"

/*******************************************************************\

Function: update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void update()
{
  deltarepo_configt config;

  switch(config.kind)
  {
  case NONE: assert(false); break;  
  
  case GIT:
    {
    }
    break;
    
  case SVN:
    {
      
    }
    break;
  }
}
