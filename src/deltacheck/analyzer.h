/*******************************************************************\

Module: Main Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_CHECKER_H
#define CPROVER_DELTACHECK_CHECKER_H

class message_handlert;
class indext;

void deltacheck_analyzer(
  const indext &index1,
  const indext &index2,
  const optionst &options,
  message_handlert &);

void one_program_analyzer(
  const indext &index,
  const optionst &options,
  message_handlert &);

#endif
