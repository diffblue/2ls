/*******************************************************************\

Module: Source Code Diffing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <fstream>
#include <cctype>
#include <cstdlib>

#ifdef DEBUG
#include <iostream>
#endif

#if defined(__linux__) || defined(__FreeBSD_kernel__) || defined(__CYGWIN__) || defined(__MACH__)
#include <unistd.h>
#endif

#include <util/tempfile.h>

#include "get_source.h"

/*******************************************************************\

Function: diff_action

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class diff_actiont
{
public:
  char action;
  unsigned old_from, old_to, old_size;
  unsigned new_from, new_to, new_size;
  diff_actiont(const std::string &);

  void output(std::ostream &out)
  {
    if(action!=0)
      out << "Action: " << action
          << " Old: " << old_from << "-" << old_to << " (" << old_size << ")"
          << " New: " << new_from << "-" << new_to << " (" << new_size << ")"
          << "\n";
  }
};

diff_actiont::diff_actiont(const std::string &src)
{
  old_from=old_to=new_from=new_to=old_size=new_size=0;
  action=0;

  // e.g. 4,5c4
  if(src.empty() || !isdigit(src[0])) return;
  
  std::string old_from_str, old_to_str, new_from_str, new_to_str;

  unsigned i;

  for(i=0; i<src.size() && isdigit(src[i]); i++) old_from_str+=src[i];

  if(i<src.size() && src[i]==',')
    for(i++; i<src.size() && isdigit(src[i]); i++) old_to_str+=src[i];
  else
    old_to_str=old_from_str;
    
  if(i<src.size() && isalpha(src[i]))
    action=src[i];
  else
    return;

  for(i++; i<src.size() && isdigit(src[i]); i++) new_from_str+=src[i];

  if(i<src.size() && src[i]==',')
    for(i++; i<src.size() && isdigit(src[i]); i++) new_to_str+=src[i];
  else
    new_to_str=new_from_str;

  old_from=atoi(old_from_str.c_str());
  old_to=atoi(old_to_str.c_str());
  new_from=atoi(new_from_str.c_str());
  new_to=atoi(new_to_str.c_str());
  
  old_size=old_to-old_from+1;
  new_size=new_to-new_from+1;
  
  if(action=='a')
    old_size=0;
  else if(action=='d')
    new_size=0;

  // sanity check
  if(old_from>old_to || new_from>new_to) action=0;
}
  
/*******************************************************************\

Function: process_diff

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void process_diff(
  std::list<linet> &lines1,
  std::list<linet> &lines2,
  const std::list<std::string> &diff)
{
  // constant-time access to the list of lines members
  std::vector<std::list<linet>::iterator> l_it1, l_it2;
  
  l_it1.reserve(lines1.size());
  l_it2.reserve(lines2.size());
  
  for(std::list<linet>::iterator it=lines1.begin();
      it!=lines1.end(); it++)
    l_it1.push_back(it);

  for(std::list<linet>::iterator it=lines2.begin();
      it!=lines2.end(); it++)
    l_it2.push_back(it);

  // now process the diff
  for(std::list<std::string>::const_iterator
      d_it=diff.begin();
      d_it!=diff.end();
      d_it++)
  {
    diff_actiont da(*d_it);
    
    #ifdef DEBUG
    da.output(std::cout);
    #endif

    switch(da.action)
    {
    case 'c': // change
      if(da.new_size>da.old_size)
      {
        for(unsigned i=da.old_size; i<da.new_size; i++)
        {
          assert(da.old_from<l_it1.size());
          lines1.insert(l_it1[da.old_from], linet());
        }
      }
      else if(da.old_size>da.new_size)
      {
        for(unsigned i=da.new_size; i<da.old_size; i++)
        {
          assert(da.old_from<l_it2.size());
          lines2.insert(l_it2[da.old_from], linet());
        }
      }
      break;
      
    case 'a': // add
      for(unsigned i=0; i<da.new_size; i++)
      {
        assert(da.old_from<l_it1.size());
        lines1.insert(l_it1[da.old_from], linet());
      }
      break;

    case 'd': // delete
      for(unsigned i=0; i<da.old_size; i++)
      {
        assert(da.old_from<l_it2.size());
        lines2.insert(l_it2[da.old_from], linet());
      }
      break;
    }
  }
}

/*******************************************************************\

Function: diff_it

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void diff_it(
  std::list<linet> &lines1,
  std::list<linet> &lines2)
{
  std::string tmp1_name=get_temporary_file("delta_diff1", "txt");
  std::string tmp2_name=get_temporary_file("delta_diff2", "txt");
  std::string tmp3_name=get_temporary_file("delta_diff3", "txt");

  {  
    std::ofstream out1(tmp1_name.c_str());
    std::ofstream out2(tmp2_name.c_str());
    
    for(std::list<linet>::const_iterator l_it=lines1.begin();
        l_it!=lines1.end(); l_it++)
      out1 << l_it->line << "\n";

    for(std::list<linet>::const_iterator l_it=lines2.begin();
        l_it!=lines2.end(); l_it++)
      out2 << l_it->line << "\n";
  }
  
  std::string cmdline="diff \""+tmp1_name+"\""+
                          " \""+tmp2_name+"\""+
                         "> \""+tmp3_name+"\"";
  
  system(cmdline.c_str());

  // open output
  {
    std::ifstream in(tmp3_name.c_str());
    std::string line;
    std::list<std::string> diff;
    while(std::getline(in, line)) diff.push_back(line);
    process_diff(lines1, lines2, diff);
  }
  
  // clean up
  unlink(tmp1_name.c_str());
  unlink(tmp2_name.c_str());
  unlink(tmp3_name.c_str());
}

