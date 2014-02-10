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

  // unique identifier
  std::string id;

  // stuff about the commit
  std::string commit;
  std::string message;
  std::string author;
  std::string date;
  
  unsigned added, deleted;

  // analysis status
  enum statust { WAITING, RUNNING, FAILURE, COMPLETED };
  enum staget { INIT, CHECK_OUT, BUILD, ANALYSE, DONE };
  statust status;
  staget stage;
  
  std::string hostname;
  
  void read();
  void write();
  
  void clear()
  {
    commit="";
    status=WAITING;
    stage=INIT;
    added=deleted=0;
  }
  
  void next_stage();
  
  std::string get_wd() const
  {
    return "jobs/"+id+".wd";
  }
  
  void set_hostname();
  
protected:
};

std::string as_string(job_statust::statust);
std::string as_string(job_statust::staget);

typedef std::list<job_statust> jobst;

void get_jobs(jobst &);

#endif
