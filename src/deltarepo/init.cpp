/*******************************************************************\

Module: Check out a new repository

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <iostream>
#include <fstream>

#include <sys/stat.h>

#include <util/xml.h>

#include "shell_escape.h"
#include "do_svn.h"
#include "init.h"

/*******************************************************************\

Function: sanity_check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void sanity_check(
  repo_kindt repo_kind,
  const std::string &url)
{
  switch(repo_kind)
  {
  case NONE: assert(false); break;

  case GIT:
    break;

  case SVN:
    {
      xmlt xml;
      do_svn("info "+shell_escape(url), xml);

      if(xml.name!="info")
        throw std::string("unexpected XML from svn info");
        
      xmlt::elementst::const_iterator
        entry_it=xml.find("entry");

      if(entry_it==xml.elements.end())
      {
        std::cout << xml.data << "\n";
        throw std::string("error from SVN");
      }
      
      if(entry_it->get_attribute("kind")!="dir")
        throw std::string("SVN URL is not a directory");
    }
    break;
  }
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void init(
  repo_kindt repo_kind,
  const std::string &url,
  const std::string &dest)
{
  sanity_check(repo_kind, url);

  int mkdir_result=mkdir(dest.c_str(), 0777);
  
  if(mkdir_result!=0)
    throw std::string("error creating directory `")+dest+"'";
  
  xmlt config("deltarepo");

  switch(repo_kind)
  {
  case NONE: assert(false); break;
  case GIT: config.set_attribute("kind", "git"); break;
  case SVN: config.set_attribute("kind", "svn"); break;
  }
  
  config.set_attribute("url", url);
  
  {
    std::string file_name=dest+"/"+deltarepo_configt::file_name();
    std::ofstream out_file(file_name.c_str());
    out_file << config;
  }
}
