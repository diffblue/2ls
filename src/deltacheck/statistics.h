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
  
  struct timet
  {
    timet():running(false), total(0) { }
    bool running;
    time_periodt total, last;
    absolute_timet start;
  };
  
  typedef std::map<std::string, unsigned> number_mapt;
  number_mapt number_map;

  typedef std::map<std::string, timet> time_mapt;
  time_mapt time_map;
  
  void html_report_total(std::ostream &) const;
  void html_report_last(std::ostream &) const;
  
  void clear();
  
  void start(const std::string &what);
  void stop(const std::string &what);
};

#endif
