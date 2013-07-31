/*******************************************************************\

Module: talk to SVN

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include <util/tempfile.h>
#include <util/cout_message.h>

#include <xmllang/xml_parser.h>

#include "shell_escape.h"
#include "do_git.h"

/*******************************************************************\

Function: do_svn

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_svn(const std::string &command)
{
  std::string full_command="xml "+command;

  int result=system(full_command.c_str());
  
  if(result!=0)
    throw std::string("error from svn");
}

/*******************************************************************\

Function: do_svn

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void do_svn(const std::string &command, xmlt &dest)
{
  temporary_filet temp_file("deltarepo_svn", "xml");

  std::string full_command=
    "--xml "+command+
    " > "+shell_escape(temp_file());

  do_svn(full_command);

  console_message_handlert message_handler;
  xmlt xml;

  if(parse_xml(temp_file(), message_handler, dest))
    throw std::string("failed to parse XML from SVN");

  if(xml.name!="info")
    throw std::string("unexpected XML from svn");
}
