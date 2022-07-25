/*******************************************************************\

Module: Domain utilities

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Domain utilities

#include <util/simplify_expr.h>
#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/bitvector_types.h>

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
    exprt &new_expr=to_typecast_expr(expr).op();
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
    exprt &op=to_unary_minus_expr(expr).op();
    extend_expr_types(op);

    if(op.type().id()==ID_signedbv ||
       op.type().id()==ID_unsignedbv)
    {
      typet new_type=signedbv_typet(get_bitvector_width(op)+1);
      expr=unary_minus_exprt(typecast_exprt(op, new_type), new_type);
    }
    // TODO: shall we extend floats?
    return;
  }
  if(expr.id()==ID_plus || expr.id()==ID_minus)
  {
    binary_exprt &binary=to_binary_expr(expr);
    extend_expr_types(binary.op0());
//  std::cerr << "op0: " << binary.op0() << std::endl;
    extend_expr_types(binary.op1());
//  std::cerr << "op1: " << binary.op1() << std::endl;
    unsigned size0=get_bitvector_width(binary.op0());
    unsigned size1=get_bitvector_width(binary.op1());
    assert(size0>0); assert(size1>0);
    typet new_type=binary.op0().type();
    if(binary.op0().type().id()==binary.op1().type().id())
    {
     if(new_type.id()==ID_signedbv)
       new_type=signedbv_typet(std::max(size0, size1)+1);
     else if(new_type.id()==ID_unsignedbv)
     {
       if(binary.id()==ID_minus)
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
    if(binary.id()==ID_plus)
    {
      const plus_exprt &plus=to_plus_expr(binary);
      expr=plus_exprt(
        typecast_exprt(plus.op0(), new_type),
        typecast_exprt(plus.op1(), new_type));
    }
    else if(binary.id()==ID_minus)
    {
      const minus_exprt &minus=to_minus_expr(binary);
      expr=minus_exprt(
        typecast_exprt(minus.op0(), new_type),
        typecast_exprt(minus.op1(), new_type));
    }
    else
      assert(false); // TODO: implement floats
    return;
  }
  if(expr.id()==ID_mult)
  {
    mult_exprt &mult=to_mult_expr(expr);
    extend_expr_types(mult.op0());
    extend_expr_types(mult.op1());
    unsigned size0=get_bitvector_width(mult.op0());
//    std::cerr << "expr1: " << mult.op1() << std::endl;
    unsigned size1=get_bitvector_width(mult.op1());

    assert(size0>0); assert(size1>0);
    if((mult.op0().type().id()==ID_unsignedbv ||
        mult.op0().type().id()==ID_signedbv) &&
       (mult.op1().type().id()==ID_unsignedbv ||
        mult.op1().type().id()==ID_signedbv))
    {
      typet new_type=signedbv_typet(size0+size1+1);
      expr=mult_exprt(
        typecast_exprt(mult.op0(), new_type),
        typecast_exprt(mult.op1(), new_type));
      return;
    }
    else if(mult.op0().type().id()==ID_floatbv &&
            mult.op1().type().id()==ID_floatbv)
    {
      // TODO: shall we extend floats?
    }
    else if((mult.op0().type().id()==ID_unsignedbv ||
             mult.op0().type().id()==ID_signedbv) &&
            mult.op1().type().id()==ID_floatbv)
    {
      typet new_type=mult.op1().type(); // TODO: shall we extend floats?
      expr=mult_exprt(typecast_exprt(mult.op0(), new_type), mult.op1());
      return;
    }
    else if((mult.op1().type().id()==ID_unsignedbv ||
             mult.op1().type().id()==ID_signedbv) &&
            mult.op0().type().id()==ID_floatbv)
    {
      typet new_type=mult.op0().type(); // TODO: shall we extend floats?
      expr=mult_exprt(mult.op0(), typecast_exprt(mult.op1(), new_type));
      return;
    }
    else
      assert(false);
  }
  if(expr.id()==ID_div)
  {
    div_exprt &div=to_div_expr(expr);
    extend_expr_types(div.op0());
    extend_expr_types(div.op1());
    unsigned size0=get_bitvector_width(div.op0());
    unsigned size1=get_bitvector_width(div.op1());
    assert(size0>0);
    assert(size1>0);
    if((div.op0().type().id()==ID_unsignedbv ||
        div.op0().type().id()==ID_signedbv) &&
       (div.op1().type().id()==ID_unsignedbv ||
        div.op1().type().id()==ID_signedbv))
    {
      typet new_type;
      if(div.op0().type().id()==ID_unsignedbv &&
         div.op0().type().id()==ID_unsignedbv)
        new_type=unsignedbv_typet(std::max(size0, size1));
      else if(div.op0().type().id()==ID_signedbv &&
              div.op0().type().id()==ID_unsignedbv)
        new_type=signedbv_typet(size0>size1 ? size0 : size1+1);
      else
        new_type=signedbv_typet(size0>=size1 ? size0+1 : size1);

      expr=div_exprt(
        typecast_exprt(div.op0(), new_type),
        typecast_exprt(div.op1(), new_type));
      return;
    }
    else if(div.op0().type().id()==ID_floatbv ||
            div.op1().type().id()==ID_floatbv)
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
    to_integer(to_constant_expr(expr), v);
    return v;
  }
  if(expr.id()==ID_typecast)
  {
    const exprt &op=to_typecast_expr(expr).op();
    assert(op.type().id()==ID_signedbv || op.type().id()==ID_unsignedbv);
    return simplify_const_int(op);
  }
  if(expr.id()==ID_unary_minus)
    return -simplify_const_int(to_unary_minus_expr(expr).op());
  if(expr.id()==ID_plus)
  {
    const plus_exprt &plus=to_plus_expr(expr);
    return simplify_const_int(plus.op0())+simplify_const_int(plus.op1());
  }
  if(expr.id()==ID_minus)
  {
    const minus_exprt &minus=to_minus_expr(expr);
    return simplify_const_int(minus.op0())-simplify_const_int(minus.op1());
  }
  if(expr.id()==ID_mult)
  {
    const mult_exprt &mult=to_mult_expr(expr);
    return simplify_const_int(mult.op0())*simplify_const_int(mult.op1());
  }
  if(expr.id()==ID_div)
  {
    const div_exprt &div=to_div_expr(expr);
    mp_integer d=simplify_const_int(div.op1());
    assert(d!=0);
    return simplify_const_int(div.op0())/d;
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
      auto index=numeric_cast_v<unsigned>(mp_index); // TODO: might overflow
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
    const exprt &op=to_typecast_expr(expr).op();
    if(op.type().id()==ID_signedbv || op.type().id()==ID_unsignedbv)
    {
      ieee_floatt v;
      v.from_integer(simplify_const_int(op));
      return v;
    }
    if(op.type().id()==ID_floatbv)
    {
      return ieee_floatt(simplify_const(op));
    }
    assert(false);
  }
  if(expr.id()==ID_unary_minus)
  {
    ieee_floatt v=simplify_const_float(to_unary_minus_expr(expr).op());
    v.set_sign(!v.get_sign());
    return v;
  }
  if(expr.id()==ID_plus)
  {
    const plus_exprt &plus=to_plus_expr(expr);
    ieee_floatt v1=simplify_const_float(plus.op0());
    ieee_floatt v2=simplify_const_float(plus.op1());
    v1+=v2;
    return v1;
  }
  if(expr.id()==ID_minus)
  {
    const minus_exprt &minus=to_minus_expr(expr);
    ieee_floatt v1=simplify_const_float(minus.op0());
    ieee_floatt v2=simplify_const_float(minus.op1());
    v1-=v2;
    return v1;
  }
  if(expr.id()==ID_mult)
  {
    const mult_exprt &mult=to_mult_expr(expr);
    ieee_floatt v1=simplify_const_float(mult.op0());
    ieee_floatt v2=simplify_const_float(mult.op1());
    v1*=v2;
    return v1;
  }
  if(expr.id()==ID_div)
  {
    const div_exprt &div=to_div_expr(expr);
    ieee_floatt v1=simplify_const_float(div.op0());
    ieee_floatt v2=simplify_const_float(div.op1());
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
      auto index=numeric_cast_v<unsigned>(mp_index); // TODO: might overflow
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
    expr=to_typecast_expr(expr).op();
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
        const implies_exprt &implies=to_implies_expr(*it);
        out << from_expr(ns, "", implies.op0()) << "==> ";
        if(implies.op1().id()==ID_gt)
          out << from_expr(ns, "", to_binary_expr(implies.op1()).op0());
        else if(implies.op1().id()==ID_or) // needed for lexicographic ones
        {
          forall_operands(it_lex, implies.op1())
          {
            if(it_lex->id()==ID_and)
            {
              if(it_lex==implies.op1().operands().begin())
                out << "(";
              else
                out << "\n   " << "       " << ", ";
              out << from_expr(ns, "", to_and_expr(*it_lex).op0());
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
          out << from_expr(ns, "", implies.op1());
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
      const implies_exprt &implies=to_implies_expr(expr);
      if(implies.op1().id()==ID_gt)
      {
        const binary_exprt &gt=to_binary_expr(implies.op1());
        out << from_expr(ns, "", implies.op0()) << "==> "
            << from_expr(ns, "", gt.op0());
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
    binary_exprt &less=to_binary_expr(expr);
    if(less.op0().id()==ID_unary_minus &&
       to_unary_minus_expr(less.op0()).op().id()==ID_typecast &&
       less.op1().id()==ID_constant)
    {
      const unary_minus_exprt &minus=to_unary_minus_expr(less.op0());
      const typecast_exprt &typecast=to_typecast_expr(minus.op());
      exprt lhs=typecast.op();
      clean_expr(lhs);
      const constant_exprt &rhs=to_constant_expr(less.op1());
      mp_integer c;
      to_integer(rhs, c);
      expr=binary_relation_exprt(lhs, ID_ge, from_integer(-c, lhs.type()));
    }
    else
    {
      clean_expr(less.op0());
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

/// Replaces usages of a symbol with another symbol in the given expression.
void replace_symbol(exprt &expr, const irep_idt &old, const irep_idt &updated)
{
  if(expr.id()==ID_symbol)
  {
    auto &symbol_expr=to_symbol_expr(expr);
    if(symbol_expr.get_identifier()==old)
      symbol_expr.set_identifier(updated);
  }
  else
    for(auto &op : expr.operands())
      replace_symbol(op, old, updated);
}
