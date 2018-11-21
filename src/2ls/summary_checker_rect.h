/* 
 * File:   summary_checker_rect.h
 * Author: sarbojit
 *
 * Created on 21 March, 2018, 7:13 PM
 */

#ifndef SUMMARY_CHECKER_RECT_H
#define SUMMARY_CHECKER_RECT_H

#include "summary_checker_ai.h"

class summary_checker_rect:public summary_checker_ait
{
public:
  explicit summary_checker_rect(optionst &_options,
  const ssa_heap_analysist &heap_analysis):
  summary_checker_ait(_options, heap_analysis)
  {
  }
        
  virtual resultt operator()(const goto_modelt &);
protected:
  void summarize(const goto_modelt &, bool, bool);
};

#endif /* SUMMARY_CHECKER_RECT_H */

