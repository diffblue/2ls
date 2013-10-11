/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARSEOPTIONS_H
#define CPROVER_DELTACHECK_PARSEOPTIONS_H

#include <util/ui_message.h>
#include <util/parseoptions.h>
#include <util/options.h>

#include <goto-programs/goto_functions.h>
#include <cbmc/xml_interface.h>

#define DELTACHECK_OPTIONS \
  "(function):" \
  "(debug-level):" \
  "(xml-ui)(xml-interface)" \
  "(verbosity):(version)(index):(description):" \
  "(bounds-check)(pointer-check)(div-by-zero-check)" \
  "(signed-overflow-check)(unsigned-overflow-check)(nan-check)" \
  "(show-ssa)(show-defs)(show-guards)(show-fixed-points)" \
  "(show-properties)(show-change-impact)(show-diff)" \
  "(sat)"

class deltacheck_parseoptionst:
  public parseoptions_baset,
  public xml_interfacet,
  public messaget
{
public:
  virtual int doit();
  virtual void help();

  deltacheck_parseoptionst(
    int argc, const char **argv);

protected:
  virtual void register_languages();

  virtual void get_command_line_options(optionst &options);

  void eval_verbosity();
  
  ui_message_handlert ui_message_handler;
};

#endif
