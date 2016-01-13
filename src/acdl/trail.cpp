/*******************************************************************\

Module: Trail datastructure used for backtracking. It stores 
assignment history and allows retrieval of past variable values

Author: Rajdeep Mukherjee, Peter Schrammel

\*******************************************************************/

class backtrack_trailt : public messaget
{
public:

  explicit backtrack_trailt(const optionst &_options,
    acdl_domaint &_domain)
    : 
    options(_options),
    domain(_domain)
    {
    }  

  ~backtrack_trailt() 
    {
    }

  void assign(const acdl_domaint& );

  // backtrack one deduction
  void backtrack_once();
  
  // backtrack to just before trail index
  void backtrack_to_idx(unsigned idx);

  // backtrack to decision level
  void backtrack_to_lvl(unsigned idx);

  const acdl_domaint::valuet& dlevel0_values(){
    return values_dlevel0;
  }

  // returns the value of a variable before trail index idx
  acdl_domaint::valuet value_before(
    unsigned var, unsigned idx);
  
 unsigned dlevel() { return control.size(); }

protected: 
  acdl_domaint& dom;
  acdl_domaint::valuet& values;
  acdl_domaint::valuet values_dlevel0;

  std::vector<int> control;
  std::vector<int> dlevels;
  std::vector<acdl_domaint::valuet> prev_values;
};
