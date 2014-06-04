#ifndef CPROVER_CONCRETE_TRANSFORMER_H
#define CPROVER_CONCRETE_TRANSFORMER_H

struct concrete_transformert
{

  enum Kind { equality, constraint } kind;
  
  exprt op0, op1;

  concrete_transformert(const exprt& __op0, 
                        const exprt& __op1=nil_exprt())
                        : kind(__op1.is_nil()?constraint:equality),
                          op0(__op0),
                          op1(__op1)
                          {
                          }
                                                    
  inline bool is_equality() const {return kind==equality; }
  inline bool is_constraint() const {return kind==constraint; }
  inline exprt& lhs()  { assert(is_equality()); return op0; }
  inline exprt& rhs()  { assert(is_equality()); return op1; }
  inline exprt& expr() { assert(is_constraint()); return op0; }
};

#endif
