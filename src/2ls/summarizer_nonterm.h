/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#ifndef SUMMARIZER_NONTERM_H
#define SUMMARIZER_NONTERM_H

#include "../2ls/summary_checker_base.h"

class summarizer_nonterm : public summary_checker_baset {
public:
    inline summarizer_nonterm(optionst &_options):
        summary_checker_baset(_options)
    {
    }
    void check_nontermination(const goto_modelt &);
    
    void abc(void);
private:

};

#endif /* SUMMARIZER_NONTERM_H */

