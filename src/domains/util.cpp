/*******************************************************************\

Module: Domain utilities

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Domain utilities

#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>

#include "util.h"

/// increases bitvector sizes such that there are no overflows
unsigned get_bitvector_width(const exprt &expr)
{
  return to_bitvector_type(expr.type()).get_width();
}

/// increases bitvector sizes such that there are no overflows
void extend_expr_types(exprt &expr)
{
//  std::cerr << "expr: " << expr << std::endl;
  if(expr.id()==ID_typecast)
  {
    exprt new_expr=expr.op0();
    extend_expr_types(new_expr);
    expr=new_expr;
    return;
  }
  if(expr.id()==ID_constant ||
     expr.id()==ID_symbol ||
     expr.id()==ID_index)
    return;
  if(expr.id()==ID_unary_minus)
  {
    extend_expr_types(expr.op0());

    if(expr.op0().type().id()==ID_signedbv ||
       expr.op0().type().id()==ID_unsignedbv)
    {
      typet new_type=signedbv_typet(get_bitvector_width(expr.op0())+1);
      expr=unary_minus_exprt(typecast_exprt(expr.op0(), new_type), new_type);
    }
    // TODO: shall we extend floats?
    return;
  }
  if(expr.id()==ID_plus || expr.id()==ID_minus)
  {
    extend_expr_types(expr.op0());
//  std::cerr << "op0: " << expr.op0() << std::endl;
    extend_expr_types(expr.op1());
//  std::cerr << "op1: " << expr.op1() << std::endl;
    unsigned size0=get_bitvector_width(expr.op0());
    unsigned size1=get_bitvector_width(expr.op1());
    assert(size0>0); assert(size1>0);
    typet new_type=expr.op0().type();
    if(expr.op0().type().id()==expr.op1().type().id())
    {
     if(new_type.id()==ID_signedbv)
       new_type=signedbv_typet(std::max(size0, size1)+1);
     else if(new_type.id()==ID_unsignedbv)
     {
       if(expr.id()==ID_minus)
         new_type=signedbv_typet(std::max(size0, size1)+1);
       else
         new_type=unsignedbv_typet(std::max(size0, size1)+1);
     }
     else if(new_type.id()==ID_floatbv)
     {
       // TODO: shall we extend floats?
     }
     else
       assert(false);
    }
    else // operands do not have the same type
    {
     if(new_type.id()==ID_signedbv)
       new_type=signedbv_typet(size0<=size1 ? size1+2 : size0+1);
     else if(new_type.id()==ID_unsignedbv)
       new_type=signedbv_typet(size1<=size0 ? size0+2 : size1+1);
     else
       assert(false); // TODO: implement floats
    }
    if(expr.id()==ID_plus)
      expr=plus_exprt(
        typecast_exprt(expr.op0(), new_type),
        typecast_exprt(expr.op1(), new_type));
    else if(expr.id()==ID_minus)
    {
      expr=minus_exprt(
        typecast_exprt(expr.op0(), new_type),
        typecast_exprt(expr.op1(), new_type));
    }
    else
      assert(false); // TODO: implement floats
    return;
  }
  if(expr.id()==ID_mult)
  {
    extend_expr_types(expr.op0());
    extend_expr_types(expr.op1());
    unsigned size0=get_bitvector_width(expr.op0());
//    std::cerr << "expr1: " << expr.op1() << std::endl;
    unsigned size1=get_bitvector_width(expr.op1());

    assert(size0>0); assert(size1>0);
    if((expr.op0().type().id()==ID_unsignedbv ||
        expr.op0().type().id()==ID_signedbv) &&
       (expr.op1().type().id()==ID_unsignedbv ||
        expr.op1().type().id()==ID_signedbv))
    {
      typet new_type=signedbv_typet(size0+size1+1);
      expr=mult_exprt(
        typecast_exprt(expr.op0(), new_type),
        typecast_exprt(expr.op1(), new_type));
      return;
    }
    else if(expr.op0().type().id()==ID_floatbv &&
            expr.op1().type().id()==ID_floatbv)
    {
      // TODO: shall we extend floats?
    }
    else if((expr.op0().type().id()==ID_unsignedbv ||
             expr.op0().type().id()==ID_signedbv) &&
            expr.op1().type().id()==ID_floatbv)
    {
      typet new_type=expr.op1().type(); // TODO: shall we extend floats?
      expr=mult_exprt(typecast_exprt(expr.op0(), new_type), expr.op1());
      return;
    }
    else if((expr.op1().type().id()==ID_unsignedbv ||
             expr.op1().type().id()==ID_signedbv) &&
            expr.op0().type().id()==ID_floatbv)
    {
      typet new_type=expr.op0().type(); // TODO: shall we extend floats?
      expr=mult_exprt(expr.op0(), typecast_exprt(expr.op1(), new_type));
      return;
    }
    else
      assert(false);
  }
  if(expr.id()==ID_div)
  {
    extend_expr_types(expr.op0());
    extend_expr_types(expr.op1());
    unsigned size0=get_bitvector_width(expr.op0());
    unsigned size1=get_bitvector_width(expr.op1());
    assert(size0>0);
    assert(size1>0);
    if((expr.op0().type().id()==ID_unsignedbv ||
        expr.op0().type().id()==ID_signedbv) &&
       (expr.op1().type().id()==ID_unsignedbv ||
        expr.op1().type().id()==ID_signedbv))
    {
      typet new_type;
      if(expr.op0().type().id()==ID_unsignedbv &&
         expr.op0().type().id()==ID_unsignedbv)
        new_type=unsignedbv_typet(std::max(size0, size1));
      else if(expr.op0().type().id()==ID_signedbv &&
              expr.op0().type().id()==ID_unsignedbv)
        new_type=signedbv_typet(size0>size1 ? size0 : size1+1);
      else
        new_type=signedbv_typet(size0>=size1 ? size0+1 : size1);

      expr=div_exprt(
        typecast_exprt(expr.op0(), new_type),
        typecast_exprt(expr.op1(), new_type));
      return;
    }
    else if(expr.op0().type().id()==ID_floatbv ||
            expr.op1().type().id()==ID_floatbv)
    {
      // TODO: shall we extend floats?
      return;
    }
    else
      assert(false);
  }
  std::cerr << "failed expr: " << expr.pretty() << std::endl;
  assert(false);
}

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
    const exprt &op0=expr.op0();
    assert(op0.type().id()==ID_signedbv || op0.type().id()==ID_unsignedbv);
    return simplify_const_int(op0);
  }
  if(expr.id()==ID_unary_minus)
    return -simplify_const_int(expr.op0());
  if(expr.id()==ID_plus)
    return simplify_const_int(expr.op0())+simplify_const_int(expr.op1());
  if(expr.id()==ID_minus)
    return simplify_const_int(expr.op0())-simplify_const_int(expr.op1());
  if(expr.id()==ID_mult)
    return simplify_const_int(expr.op0())*simplify_const_int(expr.op1());
  if(expr.id()==ID_div)
  {
    mp_integer d=simplify_const_int(expr.op1());
    assert(d!=0);
    return simplify_const_int(expr.op0())/d;
  }
  if(expr.id()==ID_symbol)
  {
#if 0
    std::cout << "substituting default value for " << expr << std::endl;
#endif
    return 0; // default value if not substituted in expr
  }
  if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const typet &array_type=to_array_type(index_expr.array().type()).subtype();
    if(array_type.id()==ID_signedbv || array_type.id()==ID_unsignedbv)
    {
      mp_integer mp_index=simplify_const_int(index_expr.index());
      unsigned index=integer2unsigned(mp_index); // TODO: might overflow
      assert(index<(index_expr.array().operands().size()));
      return simplify_const_int(index_expr.array().operands()[index]);
    }
    assert(false); // not implemented
  }
  assert(false); // not implemented
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
    const exprt &op0=expr.op0();
    if(op0.type().id()==ID_signedbv || op0.type().id()==ID_unsignedbv)
    {
      ieee_floatt v;
      v.from_integer(simplify_const_int(op0));
      return v;
    }
    if(op0.type().id()==ID_floatbv)
    {
      return ieee_floatt(simplify_const(op0));
    }
    assert(false);
  }
  if(expr.id()==ID_unary_minus)
  {
    ieee_floatt v=simplify_const_float(expr.op0());
    v.set_sign(!v.get_sign());
    return v;
  }
  if(expr.id()==ID_plus)
  {
    ieee_floatt v1=simplify_const_float(expr.op0());
    ieee_floatt v2=simplify_const_float(expr.op1());
    v1+=v2;
    return v1;
  }
  if(expr.id()==ID_minus)
  {
    ieee_floatt v1=simplify_const_float(expr.op0());
    ieee_floatt v2=simplify_const_float(expr.op1());
    v1-=v2;
    return v1;
  }
  if(expr.id()==ID_mult)
  {
    ieee_floatt v1=simplify_const_float(expr.op0());
    ieee_floatt v2=simplify_const_float(expr.op1());
    v1*=v2;
    return v1;
  }
  if(expr.id()==ID_div)
  {
    ieee_floatt v1=simplify_const_float(expr.op0());
    ieee_floatt v2=simplify_const_float(expr.op1());
    v1/=v2;
    return v1;
  }
  if(expr.id()==ID_symbol)  // default value if not substituted in expr
  {
    ieee_floatt v;
    v.make_zero();
#if 0
    std::cout << "substituting default value for " << expr << std::endl;
#endif
    return v;
  }
  if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const typet &array_type=to_array_type(index_expr.array().type()).subtype();
    if(array_type.id()==ID_float)
    {
      mp_integer mp_index=simplify_const_int(index_expr.index());
      unsigned index=integer2unsigned(mp_index); // TODO: might overflow
      assert(index<(index_expr.array().operands().size()));
      return simplify_const_float(index_expr.array().operands()[index]);
    }
    assert(false); // not implemented
  }
  assert(false); // not implemented
}

constant_exprt simplify_const(const exprt &expr)
{
//  std::cerr << "const: " << expr << std::endl;
  if(expr.id()==ID_constant)
    return to_constant_expr(expr);
  // TODO: handle "address_of" constants
  if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);
    const typet &array_type=to_array_type(index_expr.array().type()).subtype();
    if(array_type.id()==ID_signedbv)
    {
      mp_integer res=simplify_const_int(index_expr);
      const signedbv_typet &type=to_signedbv_type(expr.type());
      assert(res>=type.smallest());
      assert(res<=type.largest());
      return to_constant_expr(from_integer(res, expr.type()));
    }
    if(array_type.id()==ID_unsignedbv)
    {
      mp_integer res=simplify_const_int(index_expr);
      const unsignedbv_typet &type=to_unsignedbv_type(expr.type());
      assert(res>=type.smallest());
      assert(res<=type.largest());
      return to_constant_expr(from_integer(res, expr.type()));
    }
    if(array_type.id()==ID_float)
      return to_constant_expr(simplify_const_float(index_expr).to_expr());
    assert(false); // not implemented
  }
  //  if(expr.id()==ID_typecast) return to_constant_expr(expr.op0());
  if(expr.type().id()==ID_signedbv)
  {
    mp_integer res=simplify_const_int(expr);
    const signedbv_typet &type=to_signedbv_type(expr.type());
    assert(res>=type.smallest());
    assert(res<=type.largest());
    return to_constant_expr(from_integer(res, expr.type()));
  }
  if(expr.type().id()==ID_unsignedbv)
  {
    mp_integer res=simplify_const_int(expr);
    const unsignedbv_typet &type=to_unsignedbv_type(expr.type());
    assert(res>=type.smallest());
    assert(res<=type.largest());
    return to_constant_expr(from_integer(res, expr.type()));
  }
  if(expr.type().id()==ID_floatbv)
  {
    return to_constant_expr(simplify_const_float(expr).to_expr());
  }
  assert(false); // type not supported
}

void remove_typecast(exprt& expr)
{
  Forall_operands(it, expr)
    remove_typecast(*it);

  if(expr.id()==ID_typecast)
    expr=expr.op0();
}

/// print ranking argument expressions in a more readable format
void pretty_print_termination_argument(
  std::ostream &out,
  const namespacet &ns,
  const exprt &_expr)
{
  exprt expr=_expr;
  remove_typecast(expr);

  if(expr.id()==ID_and)
  {
    // should be of the form /\_i g_i=> R_i
    forall_operands(it, expr)
    {
      out << "\n";
      if(it==expr.operands().begin())
        out << "   ";
      else
        out << "&& ";
      if(it->id()==ID_implies)
      {
        out << from_expr(ns, "", it->op0()) << "==> ";
        if(it->op1().id()==ID_gt)
          out << from_expr(ns, "", it->op1().op0());
        else if(it->op1().id()==ID_or) // needed for lexicographic ones
        {
          forall_operands(it_lex, it->op1())
          {
            if(it_lex->id()==ID_and)
            {
              if(it_lex==it->op1().operands().begin())
                out << "(";
              else
                out << "\n   " << "       " << ", ";
              out << from_expr(ns, "", it_lex->op0());
            }
            else
            {
              out << "\n   " << "       " << ", "
                  << from_expr(ns, "", *it_lex);
            }
          }
          out << ")";
        }
        else
          out << from_expr(ns, "", it->op1());
      }
      else
        out << from_expr(ns, "", *it);
    }
    return;
  }
  else
  {
    if(expr.id()==ID_implies)
    {
      if(expr.op1().id()==ID_gt)
      {
        out << from_expr(ns, "", expr.op0()) << "==> "
            << from_expr(ns, "", expr.op1().op0());
        return;
      }
    }
  }
  out << from_expr(ns, "", expr);
}

void merge_and(
  exprt & result, const exprt &expr1, const exprt &expr2, const namespacet &ns)
{
  result=expr1;
  if(expr1!=expr2)
    result=and_exprt(expr1, expr2);
  simplify(result, ns);
}

constant_exprt make_zero(const typet &type)
{
  if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
    return from_integer(mp_integer(0), type);

  if(type.id()==ID_floatbv)
  {
    ieee_floatt cst(to_floatbv_type(type));
    cst.make_zero();
    return cst.to_expr();
  }
  if(type.id()==ID_integer)
    return constant_exprt("0", type);
  assert(false);
}

constant_exprt make_one(const typet &type)
{
  if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
    return from_integer(mp_integer(1), type);

  if(type.id()==ID_floatbv)
  {
    ieee_floatt cst(to_floatbv_type(type));
    cst.from_integer(mp_integer(1));
    return cst.to_expr();
  }
  assert(false);
}

constant_exprt make_minusone(const typet &type)
{
  if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
    return from_integer(mp_integer(-1), type);

  if(type.id()==ID_floatbv)
  {
    ieee_floatt cst(to_floatbv_type(type));
    cst.from_integer(mp_integer(1));
    cst.negate();
    return cst.to_expr();
  }
  assert(false);
}

/// retrieve original variable name from ssa variable
irep_idt get_original_name(
  const symbol_exprt &symbol_expr)
{
  std::string s=id2string(symbol_expr.get_identifier());
  std::size_t pos1=s.find_last_of("#");
  if(pos1==std::string::npos || (s.substr(pos1+1, 12)=="return_value"))
    return irep_idt(s);
  return s.substr(0, pos1);
}

void clean_expr(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    symbol_exprt &symbol_expr=to_symbol_expr(expr);
    symbol_expr.set_identifier(get_original_name(symbol_expr));
  }
  else if(expr.id()==ID_and)
  {
    Forall_operands(it, expr)
      clean_expr(*it);
  }
  else if(expr.id()==ID_le)
  {
    if(expr.op0().id()==ID_unary_minus &&
       expr.op0().op0().id()==ID_typecast &&
       expr.op1().id()==ID_constant)
    {
      exprt lhs=expr.op0().op0().op0();
      clean_expr(lhs);
      constant_exprt rhs=to_constant_expr(expr.op1());
      mp_integer c;
      to_integer(rhs, c);
      expr=binary_relation_exprt(lhs, ID_ge, from_integer(-c, lhs.type()));
    }
    else
    {
      clean_expr(expr.op0());
    }
  }
}

bool is_cprover_symbol(const exprt &expr)
{
  return expr.id()==ID_symbol &&
         has_prefix(
           id2string(to_symbol_expr(expr).get_identifier()),
           CPROVER_PREFIX);
}

/// \param id: Symbol identifier.
/// \return If the symbol is a dynamic object, then the location number of the
///   malloc call where the object was allocated, otherwise -1.
int get_dynobj_line(const irep_idt &id)
{
  std::string name=id2string(id);
  size_t pos=name.find("dynamic_object$");
  if(pos==std::string::npos)
    return -1;

  size_t start=pos+15;
  size_t end=name.find_first_not_of("0123456789", start);
  std::string number=name.substr(start, end-start);
  return std::stoi(number);
}

std::string get_dynobj_instance(const irep_idt &id)
{
  std::string name=id2string(id);
  size_t pos=name.find("dynamic_object$");
  if(pos==std::string::npos)
    return "";
  pos=name.find('$', pos+15);
  if(pos==std::string::npos)
    return "";
  size_t start=pos+1;
  size_t end=name.find_first_not_of("0123456789co", start);
  return name.substr(start, end-start);
}
