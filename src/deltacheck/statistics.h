/*******************************************************************\

Module: Statistics

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef DELTACHECK_STATISTICS_H
#define DELTACHECK_STATISTICS_H

#include <ostream>
#include <string>
#include <map>

#include <util/time_stopping.h>

class statisticst
{
public:
  inline statisticst()
  {
    clear();
  }

  unsigned functions_processed;

  struct timet
  {
    timet():running(false), total(0) { }
    bool running;
    fine_timet total, function, start;
  };

  typedef std::map<std::string, timet> time_mapt;
  time_mapt time_map;
  
  void html_report_total(std::ostream &) const;
  void html_report_function(std::ostream &) const;
  
  void clear();
  void next_function();
  
  void start(const std::string &what);
  void stop(const std::string &what);
};

#endif
