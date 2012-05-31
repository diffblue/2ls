/*******************************************************************\

Module: Command Line Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DELTACHECK_PARSEOPTIONS_H
#define CPROVER_DELTACHECK_PARSEOPTIONS_H

#include <ui_message.h>
#include <parseoptions.h>
#include <options.h>

#include <goto-programs/goto_functions.h>
//#include <langapi/language_ui.h>
#include <cbmc/xml_interface.h>

#define DELTACHECK_OPTIONS \
  "(function):" \
  "(debug-level):" \
  "(call-graph-dot):" \
  "(xml-ui)(xml-interface)(claim):" \
  "(show-goto-functions)(show-claims)" \
  "(verbosity):(version)(summarize)"

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

  // PHASE 1
  virtual int summarization(
    const optionst &options,
    const std::list<std::string> &files);

  // PHASE 2
  virtual int reporting(
    const optionst &options,
    const std::list<std::string> &files);

  void set_verbosity(messaget &message);
  
  ui_message_handlert ui_message_handler;
};

#endif
