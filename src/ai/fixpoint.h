#ifndef CPROVER_FIXPOINT_H
#define CPROVER_FIXPOINT_H

/******************************************************************************\
Fixed point iteration for abstract interpretation 
\******************************************************************************/

#include <climits>
#include <list>
#include <map>
#include <set>
#include <vector>
#include <iostream>

#define DEBUG 1

/******************************************************************************\
abstract domain interface 
\******************************************************************************/
template<class AbstractValue, class ConcreteTransformer> 
class domaint
{
 public:
  virtual AbstractValue bottom() = 0;
  // return true if v1 has changed
  virtual bool join(AbstractValue &v1, 
                    const AbstractValue &v2) = 0;
  // return true if v2 contains v1
  virtual bool widen(AbstractValue &v1, 
                     const AbstractValue &v2) = 0;
  virtual AbstractValue transform(const AbstractValue &v,
                                  const ConcreteTransformer &t) = 0;
                                  
  virtual void output(const AbstractValue &v, std::ostream& out)=0;
};

/******************************************************************************\
fixed point iteration class 
\******************************************************************************/
template<class AbstractValue, class ConcreteTransformer>
class fixpointt
{
 public:
  typedef AbstractValue resultt;
  typedef std::vector<ConcreteTransformer> systemt;
 
  fixpointt(systemt &_sys, 
            domaint<AbstractValue,ConcreteTransformer> &_domain) 
    : sys(_sys), domain(_domain) {}


  /****************************************************************************/
  void analyze(resultt &result,
               unsigned widening_start,
               unsigned widening_descend
               )
  {
#if DEBUG
    std::cout << "ascending iterations" << std::endl;
#endif
    if(run(result,widening_start,false)) return;

#if DEBUG
    std::cout << "ascending iterations with widening" << std::endl;
#endif
    run(result,UINT_MAX,true);

#if DEBUG
    std::cout << "descending iterations" << std::endl;
#endif
    run(result,widening_descend,false);
  }

  void output(std::ostream &out, resultt &result)
  {
    out << "fixpoint output: ";
    domain.output(result, out);
    out << std::endl;
  }

 protected:
  systemt &sys;
  domaint<AbstractValue,ConcreteTransformer> &domain;

  /****************************************************************************/
  bool run(resultt &result, unsigned max_iterations, bool widen) 
  {
    for(unsigned iteration=0; iteration<max_iterations; iteration++)
    {
#if DEBUG
      std::cout << "iteration " << iteration << std::endl;
#endif
      //update abstract values
      AbstractValue newv = result;
      bool change=false;
      for(typename systemt::iterator t = sys.begin(); t!=sys.end(); t++) 
      {
        AbstractValue v = domain.transform(newv,*t);
        change = domain.join(newv,v) || change;
      }
      if(change) 
      {
        //widening
	if(widen)
	{
	  if(domain.widen(result,newv))
	    return true; 
	  else
	    result = newv;
        }
      }
      else return true;
    }
    return false; //not converged
  }

};

#endif
