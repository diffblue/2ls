/*******************************************************************\

Module: Job Status

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTAGIT_JOB_STATUS_H
#define DELTAGIT_JOB_STATUS_H

#include <list>
#include <string>

class job_statust
{
public:
  explicit job_statust(const std::string &_id):id(_id)
  {
    read();
  }

  std::string id;
  std::string commit;
  std::string message;
  std::string author;
  std::string date;
  
  unsigned added, deleted;

  enum statust { INIT, CHECK_OUT, BUILD, ANALYSE, DONE };
  bool failure;
  statust status;
  
  void read();
  void write();
  
  void clear()
  {
    commit="";
    status=INIT;
    failure=false;
    added=deleted=0;
  }
  
protected:
};

std::string as_string(job_statust::statust);

typedef std::list<job_statust> jobst;

void get_jobs(jobst &);

#endif
