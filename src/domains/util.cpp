#include "util.h"


/*******************************************************************\

Function: extend_expr_types

  Inputs:

 Outputs:

 Purpose: increases bitvector sizes such that there are no overflows

\*******************************************************************/

void extend_expr_types(exprt &expr)
{
//  std::cerr << "expr: " << expr << std::endl;
  if(expr.id()==ID_typecast) assert(false);
  if(expr.id()==ID_constant) return;
  if(expr.id()==ID_symbol) return;
  if(expr.id()==ID_index) return;
  if(expr.id()==ID_unary_minus)
  {
    extend_expr_types(expr.op0());
    typet new_type = expr.op0().type();
    if(new_type.id()==ID_signedbv) 
    {
      signedbv_typet &new_typebv = to_signedbv_type(new_type);
      new_typebv.set_width(new_typebv.get_width()+1); 
    }
    else if(new_type.id()==ID_unsignedbv) 
    {
      unsignedbv_typet &old_type = to_unsignedbv_type(new_type);
      new_type = signedbv_typet(old_type.get_width()+1); 
    }
    expr = unary_minus_exprt(typecast_exprt(expr.op0(),new_type),new_type);
    return;
  }
  if(expr.id()==ID_plus || expr.id()==ID_minus)
  {
    extend_expr_types(expr.op0());
//  std::cerr << "op0: " << expr.op0() << std::endl;
    extend_expr_types(expr.op1());
//  std::cerr << "op1: " << expr.op1() << std::endl;
    unsigned size0 = 0, size1  = 0;
    if(expr.op0().type().id()==ID_signedbv) 
      size0 =  to_signedbv_type(expr.op0().type()).get_width();
    if(expr.op0().type().id()==ID_unsignedbv) 
      size0 =  to_unsignedbv_type(expr.op0().type()).get_width();
    if(expr.op1().type().id()==ID_signedbv) 
      size1 =  to_signedbv_type(expr.op1().type()).get_width();
    if(expr.op1().type().id()==ID_unsignedbv) 
      size1 =  to_unsignedbv_type(expr.op1().type()).get_width();
    assert(size0>0); assert(size1>0); //TODO: implement floats
    typet new_type = expr.op0().type();
    if(expr.op0().type().id()==expr.op1().type().id())
    {
     if(new_type.id()==ID_signedbv) 
       new_type = signedbv_typet(std::max(size0,size1)+1);
     else if(new_type.id()==ID_unsignedbv) 
     {
       if(expr.id()==ID_minus) 
         new_type = signedbv_typet(std::max(size0,size1)+1);
       else 
         new_type = unsignedbv_typet(std::max(size0,size1)+1);
     }
     else assert(false);
    }
    else
    {
     if(new_type.id()==ID_signedbv) 
       new_type = signedbv_typet(size0<=size1 ? size1+2 : size0+1);
     else if(new_type.id()==ID_unsignedbv) 
       new_type = signedbv_typet(size1<=size0 ? size0+2 : size1+1);
     else assert(false);
    }
    if(expr.id()==ID_plus)
      expr = plus_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
    else if(expr.id()==ID_minus)
      expr = minus_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
     else assert(false);
    return;
  }
  //TODO: implement mult
  if(expr.id()==ID_mult)
  {
    extend_expr_types(expr.op0());
    extend_expr_types(expr.op1());
    unsigned size0 = 0, size1  = 0;
    if(expr.op0().type().id()==ID_signedbv) 
      size0 =  to_signedbv_type(expr.op0().type()).get_width();
    if(expr.op0().type().id()==ID_unsignedbv) 
      size0 =  to_unsignedbv_type(expr.op0().type()).get_width();
    if(expr.op1().type().id()==ID_signedbv) 
      size1 =  to_signedbv_type(expr.op1().type()).get_width();
    if(expr.op1().type().id()==ID_unsignedbv) 
      size1 =  to_unsignedbv_type(expr.op1().type()).get_width();
    assert(size0>0); assert(size1>0); //TODO: implement floats
    typet new_type = signedbv_typet(size0+size1+1);
    expr = mult_exprt(typecast_exprt(expr.op0(),new_type),typecast_exprt(expr.op1(),new_type));
    return;
  }
  std::cerr << "expr: " << expr << std::endl;
  assert(false);
}



/*******************************************************************\

Function: simplify_const

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

mp_integer simplify_const_int(const exprt &expr)
{
  if(expr.id()==ID_constant) 
  {
    mp_integer v;
    to_integer(expr, v);
    return v;
  }
  if(expr.id()==ID_typecast) 
  {
    const exprt &op0 = expr.op0();
    assert(op0.type().id()==ID_signedbv || op0.type().id()==ID_unsignedbv);
    return simplify_const_int(op0);
  }
  if(expr.id()==ID_unary_minus) return -simplify_const_int(expr.op0());
  if(expr.id()==ID_plus) return simplify_const_int(expr.op0())+simplify_const_int(expr.op1());
  if(expr.id()==ID_minus) return simplify_const_int(expr.op0())-simplify_const_int(expr.op1());
  if(expr.id()==ID_mult) return simplify_const_int(expr.op0())*simplify_const_int(expr.op1());  
  if(expr.id()==ID_symbol) 
  {
    std::cout << "substituting default value for " << expr << std::endl;
    return 0; //default value if not substituted in expr
  }
  if(expr.id()==ID_index) 
  {
    const index_exprt &index_expr = to_index_expr(expr);
    const typet &array_type = to_array_type(index_expr.array().type()).subtype();
    if(array_type.id()==ID_signedbv || array_type.id()==ID_unsignedbv)
    {
      mp_integer mp_index = simplify_const_int(index_expr.index());
      unsigned index = integer2unsigned(mp_index); //TODO: might overflow
      assert(index<(index_expr.array().operands().size()));
      return simplify_const_int(index_expr.array().operands()[index]);
    }
    assert(false); //not implemented
  }
  assert(false); //not implemented
}

ieee_floatt simplify_const_float(const exprt &expr)
{
  if(expr.id()==ID_constant) 
  {
    ieee_floatt v(to_constant_expr(expr));
    return v;
  }
  if(expr.id()==ID_typecast) 
  {
    const exprt &op0 = expr.op0();
    if(op0.type().id()==ID_signedbv || op0.type().id()==ID_unsignedbv)
    {
      ieee_floatt v;
      v.from_integer(simplify_const_int(op0));
      return v; 
    }
    assert(false);
  }
  if(expr.id()==ID_unary_minus) 
  {
    ieee_floatt v = simplify_const_float(expr.op0());
    v.set_sign(!v.get_sign());
    return v; 
  }
  if(expr.id()==ID_plus) 
  {
    ieee_floatt v1 = simplify_const_float(expr.op0());
    ieee_floatt v2 = simplify_const_float(expr.op1());
    v1 += v2;
    return v1; 
  }
  if(expr.id()==ID_minus)
  {
    ieee_floatt v1 = simplify_const_float(expr.op0());
    ieee_floatt v2 = simplify_const_float(expr.op1());
    v1 -= v2;
    return v1; 
  }
  if(expr.id()==ID_mult)
  {
    ieee_floatt v1 = simplify_const_float(expr.op0());
    ieee_floatt v2 = simplify_const_float(expr.op1());
    v1 *= v2;
    return v1; 
  }
  if(expr.id()==ID_symbol)  //default value if not substituted in expr
  {
    ieee_floatt v;
    v.make_zero();

    std::cout << "substituting default value for " << expr << std::endl;

    return v; 
  }
  if(expr.id()==ID_index) 
  {
    const index_exprt &index_expr = to_index_expr(expr);
    const typet &array_type = to_array_type(index_expr.array().type()).subtype();
    if(array_type.id()==ID_float)
    {
      mp_integer mp_index = simplify_const_int(index_expr.index());
      unsigned index = integer2unsigned(mp_index); //TODO: might overflow
      assert(index<(index_expr.array().operands().size()));
      return simplify_const_float(index_expr.array().operands()[index]);
    }
    assert(false); //not implemented
  }
  assert(false); //not implemented
}

constant_exprt simplify_const(const exprt &expr)
{
  if(expr.id()==ID_constant) return to_constant_expr(expr);
  if(expr.id()==ID_index) 
  {
    const index_exprt &index_expr = to_index_expr(expr);
    const typet &array_type = to_array_type(index_expr.array().type()).subtype();
    if(array_type.id()==ID_signedbv)
    {
      mp_integer res = simplify_const_int(index_expr);
      const signedbv_typet &type = to_signedbv_type(expr.type());
      assert(res>=type.smallest());
      assert(res<=type.largest());
      return to_constant_expr(from_integer(res,expr.type()));
    }
    if(array_type.id()==ID_unsignedbv)
    {
      mp_integer res = simplify_const_int(index_expr);
      const unsignedbv_typet &type = to_unsignedbv_type(expr.type());
      assert(res>=type.smallest());
      assert(res<=type.largest());
      return to_constant_expr(from_integer(res,expr.type()));
    }
    if(array_type.id()==ID_float)
      return to_constant_expr(simplify_const_float(index_expr).to_expr());
    assert(false); //not implemented
  }
  //  if(expr.id()==ID_typecast) return to_constant_expr(expr.op0());
  if(expr.type().id()==ID_signedbv) 
  {
    mp_integer res = simplify_const_int(expr);
    const signedbv_typet &type = to_signedbv_type(expr.type());
    assert(res>=type.smallest());
    assert(res<=type.largest());
    return to_constant_expr(from_integer(res,expr.type()));
  }
  if(expr.type().id()==ID_unsignedbv)
  {
    mp_integer res = simplify_const_int(expr);
    const unsignedbv_typet &type = to_unsignedbv_type(expr.type());
    assert(res>=type.smallest());
    assert(res<=type.largest());
    return to_constant_expr(from_integer(res,expr.type()));
  }
  if(expr.type().id()==ID_floatbv)
  {
    return to_constant_expr(simplify_const_float(expr).to_expr());
  }
  assert(false); //type not supported
}

/*******************************************************************\

Function: pretty_print_termination_argument()

  Inputs:

 Outputs:

 Purpose: print ranking argument expressions in a more readable format

\******************************************************************/

void pretty_print_termination_argument(std::ostream &out, const namespacet &ns, const exprt &expr)
{
  if(expr.id()==ID_and)
  {
    // should be of the form /\_i g_i => R_i
    for(exprt::operandst::const_iterator it = expr.operands().begin(); 
      it != expr.operands().end(); it++)
    {
      out << "\n";
      if(it == expr.operands().begin()) out << "   "; 
      else out << "&& ";
      if(it->id()==ID_implies)
      {
        out << from_expr(ns,"",it->op0()) << " ==> ";
        if(it->op1().id()==ID_gt)
          out << from_expr(ns,"",it->op1().op0());
        // TODO: should the ID_and in the following line be ID_or?
        else if(it->op1().id()==ID_and) // needed for lexicographic ones
        {
          for(exprt::operandst::const_iterator it_lex = it->op1().operands().begin();
              it_lex != it->op1().operands().end(); it_lex++)
          {
            if(it_lex == it->op1().operands().begin()) out << "(";
            else out << std::endl << "   " << "     " << ",";
            //TODO: print something nicer
            out << from_expr(ns,"",*it_lex);
          }
          out << ")";
        }
        else out << from_expr(ns,"",it->op1());
      }
      else out << from_expr(ns,"",*it);
    }
    return;
  }
  else
  {
    if(expr.id()==ID_implies)
    {
      if(expr.op1().id()==ID_gt)
      {
	out << from_expr(ns,"",expr.op0()) << " ==> " << from_expr(ns,"",expr.op1().op0());
	return;
      }
    }
  }
  out << from_expr(ns,"",expr);
}
