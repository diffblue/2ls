#ifndef CPROVER_CONCRETE_TRANSFORMER_H
#define CPROVER_CONCRETE_TRANSFORMER_H

struct ssa_cfg_concrete_transformert 
{
  typedef std::vector<equal_exprt> equalitiest;
  equalitiest equalities;

  typedef std::vector<exprt> constraintst;
  constraintst constraints;
};

#endif
