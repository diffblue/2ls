/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   template_gen_rec_summary.h
 * Author: sarbojit
 *
 * Created on 19 March, 2018, 10:19 PM
 */

#ifndef TEMPLATE_GEN_REC_SUMMARY_H
#define TEMPLATE_GEN_REC_SUMMARY_H

#include "template_generator_summary.h"

class template_gen_rec_summaryt:public template_generator_summaryt {
public:
    typedef std::vector<std::pair<exprt,std::vector<exprt>>> tmpl_rename_mapt;
    explicit template_gen_rec_summaryt(
     optionst &_options,
     ssa_dbt &_ssa_db,
     ssa_local_unwindert &_ssa_local_unwinder):
     template_generator_summaryt(_options, _ssa_db, _ssa_local_unwinder)
    {
    }
    virtual void operator()(const irep_idt &function_name,
        unsigned _domain_number,
        const local_SSAt &SSA, tmpl_rename_mapt &templ_maps,
        bool forward=true, bool recursive=false);
    
    void get_renaming_maps(const irep_idt &function_name,local_SSAt SSA,
     tmpl_rename_mapt &templ_maps);
};

#endif /* TEMPLATE_GEN_REC_SUMMARY_H */

