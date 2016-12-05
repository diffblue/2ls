/*******************************************************************\

Module: Language Registration

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/mode.h>

#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>
#include <java_bytecode/java_bytecode_language.h>

#include "summarizer_parse_options.h"

/*******************************************************************\

Function: summarizer_parse_optionst::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizer_parse_optionst::register_languages()
{
  register_language(new_ansi_c_language);
//  register_language(new_cpp_language);
//  register_language(new_java_bytecode_language);
}
