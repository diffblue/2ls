#ifndef CPROVER_INTERVAL_MAP_DOMAIN
#define CPROVER_INTERVAL_MAP_DOMAIN

#include "fixpoint.h"
#include "concrete_transformer.h"
#include "interval_map.h"
#include "interval_widening.h"


/*
  There's already a class called interval_domaint in CProver.
  Therefore we're using the longer name interval_map_domaint.
 */
class interval_map_domaint : public domaint<interval_mapt, ssa_cfg_concrete_transformert>
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
  
  virtual bool is_leq(const interval_mapt &v1, const interval_mapt &v2);
  virtual interval_mapt join(const interval_mapt &v1, 
                             const interval_mapt &v2)
  {
    interval_mapt tmp(v1);
    tmp.join(v2);
    return tmp;
  }
  
  virtual interval_mapt widen(const interval_mapt &v1, 
                              const interval_mapt &v2);
  virtual interval_mapt transform(const interval_mapt &v,
                                  const ssa_cfg_concrete_transformert &t);
                                  
protected:
  interval_widening_thresholdst &interval_widening_thresholds;
  

};

#endif
