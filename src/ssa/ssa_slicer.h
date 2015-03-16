/*******************************************************************\

Module: SSA Slicer

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_SLICER_H
#define CPROVER_SSA_SLICER_H

#include <util/message.h>

#include "local_ssa.h"

class ssa_slicert : public messaget
{
 public:

  void operator()(std::list<exprt> &dest,
		  const local_SSAt &src);

  //statistics
  unsigned sliced_equalities;
  unsigned sliced_constraints;

 protected:
  typedef struct 
  {
    local_SSAt::nodet::constraintst::const_iterator constr;
    local_SSAt::nodest::const_iterator node;
  }  constr_infot;
  typedef std::list<constr_infot> constraint_sett;
  typedef struct 
  {
    local_SSAt::nodet::equalitiest::const_iterator def;
    local_SSAt::nodest::const_iterator def_node;
    constraint_sett constraints;
  } symbol_infot;
  typedef hash_map_cont<irep_idt,symbol_infot,irep_id_hash> symbol_mapt;

};

#endif
