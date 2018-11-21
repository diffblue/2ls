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
    const local_SSAt &SSA,
    exprt &merge_exprt,
    bool forward=true);
    
  void merge_vars(const irep_idt &function_name,
    const local_SSAt &SSA,
    exprt& merge_expr);
  void collect_inout_vars(const local_SSAt &SSA, bool forward);
  void instantiate_template_for_rec(local_SSAt SSA);
  replace_mapt init_vars_map;
  domaint::var_specst var_specs_no_out;
  private:
    exprt merge_guard,guard_ins;
    std::vector<symbol_exprt> in_vars_vec,out_vars_vec,rb_vars;
};

#endif /* TEMPLATE_GEN_REC_SUMMARY_H */

