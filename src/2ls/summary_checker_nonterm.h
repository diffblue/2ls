/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#ifndef SUMMARIZER_NONTERM_H
#define SUMMARIZER_NONTERM_H

#include "summary_checker_base.h"

class summary_checker_nontermt : public summary_checker_baset
{
public:
    explicit summary_checker_nontermt(optionst &_options):
        summary_checker_baset(_options)
    {
    }
    virtual resultt operator()(const goto_modelt &);

    virtual void check_properties(
      const ssa_dbt::functionst::const_iterator f_it);
};

#endif /* SUMMARIZER_NONTERM_H */

