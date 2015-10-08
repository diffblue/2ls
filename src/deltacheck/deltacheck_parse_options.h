/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARSE_OPTIONS_H
#define CPROVER_DELTACHECK_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>
#include <util/options.h>

#include <goto-programs/goto_functions.h>
#include <cbmc/xml_interface.h>

#define DELTACHECK_OPTIONS \
  "(function):" \
  "(debug-level):" \
  "(xml-ui)(xml-interface)" \
  "(verbosity):(version)(index):(description-old):(description-new):" \
  "(bounds-check)(pointer-check)(div-by-zero-check)" \
  "(signed-overflow-check)(unsigned-overflow-check)(nan-check)" \
  "(show-ssa)(show-defs)(show-guards)(show-fixed-points)" \
  "(show-properties)(show-change-impact)(show-diff)" \
  "(no-inline)(sat)"

class deltacheck_parse_optionst:
  public parse_options_baset,
  public xml_interfacet,
  public messaget
{
public:
  virtual int doit();
  virtual void help();

  deltacheck_parse_optionst(
    int argc, const char **argv);

protected:
  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);

  void eval_verbosity();
  
  ui_message_handlert ui_message_handler;
};

#endif
