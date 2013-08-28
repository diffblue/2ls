/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTAGIT_JOB_STATUS_H
#define DELTAGIT_JOB_STATUS_H

#include <string>

class job_statust
{
public:
  job_statust(const std::string &_id):id(_id)
  {
    read();
  }

  std::string id;

  enum statust { NEW, CHECKED_OUT, BUILT, DONE };
  statust status;
  
  void read();
  void write();

protected:
};

std::string as_string(job_statust::statust);

#endif
