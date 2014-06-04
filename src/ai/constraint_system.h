#ifndef CPROVER_CONSTRAINT_SYSTEM_H
#define CPROVER_CONCRETE_TRANSFORMER_H

struct constraint_systemt 
{
  typedef std::vector<equal_exprt> equalitiest;
  equalitiest equalities;

  typedef std::vector<exprt> constraintst;
  constraintst constraints;
};

#endif
