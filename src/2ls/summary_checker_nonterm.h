/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#ifndef SUMMARIZER_NONTERM_H
#define SUMMARIZER_NONTERM_H

#include "summary_checker_base.h"

class summary_checker_nontermt : public summary_checker_baset {
public:
    inline summary_checker_nontermt(optionst &_options):
        summary_checker_baset(_options)
    {
    }
    virtual resultt operator()(const goto_modelt &);

private:

};

#endif /* SUMMARIZER_NONTERM_H */

