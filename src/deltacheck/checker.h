/*******************************************************************\

Module: Main Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CHECKER_H
#define CPROVER_DELTACHECK_CHECKER_H

class message_handlert;
class indext;

void delta_check(
  const indext &index1,
  const indext &index2,
  message_handlert &);

void one_program_check(
  const indext &index,
  message_handlert &);

#endif
