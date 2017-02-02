/*******************************************************************\

Module: Summarizer for Nontermination Bit-level analysis

Author: Stefan Marticek

\*******************************************************************/

#include <iostream>

#include "summarizer_nonterm.h"

#include "../ssa/ssa_var_collector.h"

void summarizer_nonterm::check_nontermination(const goto_modelt &)
{
    std::cout << "\n\n**********First run**************\n\n";
}