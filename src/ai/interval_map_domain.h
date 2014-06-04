#ifndef CPROVER_INTERVAL_MAP_DOMAIN
#define CPROVER_INTERVAL_MAP_DOMAIN

#include "fixpoint.h"
#include "concrete_transformers.h"
#include "interval_map.h"
#include "interval_widening.h"

class interval_map_domaint : public domaint<interval_mapt, concrete_transformert>
{
public:

  interval_map_domaint(interval_widening_thresholdst &__interval_widening_thresholds)
    : interval_widening_thresholds(__interval_widening_thresholds) 
    {}

  virtual ~interval_map_domaint();

  virtual interval_mapt bottom() 
  { 
    return interval_mapt(); 
  }
  
  void initialise(interval_mapt&, const concrete_transformerst &transformers);
  
  // return true if v1 has changed
  virtual bool join(interval_mapt &v1, 
                    const interval_mapt &v2)
  {
    return v1.join(v2);
  }
  
  // return true if v2 contains v1
  virtual bool widen(interval_mapt &v1, 
                     const interval_mapt &v2);
                     
  virtual interval_mapt transform(const interval_mapt &v,
                                  const concrete_transformert &t);
   
   
  virtual void output(const interval_mapt &v, std::ostream& out);
                                  
                                                                    
  static bool is_int(const typet &src)
  {
    return src.id()==ID_signedbv || src.id()==ID_unsignedbv;
  }

  static bool is_float(const typet &src)
  {
    return src.id()==ID_floatbv;
  }

  
                            
protected:
  interval_widening_thresholdst &interval_widening_thresholds;
};

#endif
