/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   summarizer_rec_fwt.h
 * Author: sarbojit
 *
 * Created on 13 March, 2018, 4:52 PM
 */

#ifndef SUMMARIZER_REC_FWT_H
#define SUMMARIZER_REC_FWT_H

#include <util/message.h>
#include <util/options.h>
#include <util/time_stopping.h>

#include <ssa/ssa_inliner.h>
#include <ssa/ssa_unwinder.h>
#include <ssa/local_ssa.h>
#include <ssa/ssa_db.h>

#include "summarizer_fw.h"

class summarizer_rec_fwt:public summarizer_fwt {
public:
    explicit summarizer_rec_fwt(optionst &_options,
    summary_dbt &_summary_db,
    ssa_dbt &_ssa_db,
    ssa_unwindert &_ssa_unwinder,
    ssa_inlinert &_ssa_inliner):
    summarizer_fwt(
      _options, _summary_db, _ssa_db, _ssa_unwinder, _ssa_inliner)
  {
  }
protected:
    virtual void compute_summary_rec(const function_namet &,
            const exprt &, bool);

    virtual void do_summary(const function_namet &,
     local_SSAt &SSA, summaryt &summary, exprt cond,
     bool context_sensitive, bool recursive);
};

#endif /* SUMMARIZER_REC_FWT_H */

