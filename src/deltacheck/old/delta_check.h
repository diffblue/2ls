/*******************************************************************\

Module: Delta Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTA_CHECK_H
#define CPROVER_DELTA_CHECK_H

class message_handlert;
class indext;

void delta_check(
  const indext &index1,
  const indext &index2,
  message_handlert &);

#endif
