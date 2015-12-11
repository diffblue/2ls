/*******************************************************************\

Module: Trail data structure used for backtracking. It stores 
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

 
