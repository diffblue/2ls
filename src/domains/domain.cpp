#include "domain.h"


domaint::kindt domaint::merge_kinds(kindt k1, kindt k2)
{
  return (k1==OUT || 
	  k2==OUT ?  (k1==LOOP || 
		      k2==LOOP ?  OUTL : OUT) :
	  (k1==LOOP || k2==LOOP ? LOOP :  IN));
}

void domaint::output_var_specs(std::ostream &out, const var_specst &var_specs,
		      const namespacet &ns)
{ 
  for(var_specst::const_iterator v = var_specs.begin(); 
      v!=var_specs.end(); v++)
    {
      switch(v->kind)
	{
	case LOOP:
	  out << "(LOOP) [ " << from_expr(ns,"",v->pre_guard) << " | ";
	  out << from_expr(ns,"",v->post_guard) << " ]: ";
	  break;
	case IN: out << "(IN)   "; break;
	case OUT: case OUTL:
	  out << "(OUT)  "; 
	  out << from_expr(ns,"",v->post_guard) << ": ";
	  break;
	default: assert(false);
	}
      out << from_expr(ns,"",v->var) << std::endl;
    }
}
