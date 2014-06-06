typedef symbol_exprt loopvart;
typedef std::set<std::pair<loopvart,loopvart> > loopvarst;
typedef std::pair<symbol_exprt, bool> multiplexer_statet;

class invt
{
  
  invt(const local_SSAt &program, loopvarst loopvars, 
    template_domaint &template_domain) {}

  void solve(invariantt &inv)
  {
    strategyt strategy;
    while(strategy_solver.improve(inv,strategy))
    {
      strategy_solver.solve(inv,strategy);
    }
  }

 protected:
  strategy_solvert strategy_solver;

};
