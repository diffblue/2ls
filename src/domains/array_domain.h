/*******************************************************************\

Module: Abstract domain for representing contents of arrays

Author: Viktor Malik <viktor.malik@gmail.com>

\*******************************************************************/
/// \file
/// Abstract domain for representing contents of arrays

#ifndef CPROVER_2LS_DOMAINS_ARRAY_DOMAIN_H
#define CPROVER_2LS_DOMAINS_ARRAY_DOMAIN_H

#include <ssa/local_ssa.h>

#include "simple_domain.h"
#include "template_generator_base.h"

/// Abstract domain for representing contents of arrays
///
/// The domain is based on splitting the array into several segments and then
/// inferring a single invariant for each segment that holds for all elements of
/// the segment.
///
/// The segmentation is done based on array_index_analysist. The analysis
/// collects all expressions that occur as array indices, distinguishing between
/// read (occurring on RHS) and write (occurring on LHS) accesses.
///
/// Written indices are used for segmentation. If all written indices
/// (say i_1, ..., i_n) for an array can be ordered (this is determined using
/// the SMT solver), the array is split into the following segments:
///
///   {0} ... {i_1} ... {i_1+1} [...] {i_n} ... {i_n+1} ... {array size}
///
/// If there is no unique ordering over the indices, there are multiple
/// segmentations created (one for each written index):
///
///   {0} ... {i_1} ... {i_1+1} ... {array size}
///   [...]
///   {0} ... {i_n} ... {i_n+1} ... {array size}
///
/// In addition, a segment representing the entire array is always added.
/// Note that the segmentation is unique for each loop and depends only on
/// indices written inside that loop.
///
/// For each segment S, two fresh variables are introduced:
/// - index variable idx#S representing all array indices within the segment
/// - element variable elem#S representing all array elements (i.e.
///   array[idx#S]) within the segment.
/// Also, each segment has a lower (low#S) and upper (upp#S) bound.
///
/// The template for a segment has the (simplified) form:
///
///   idx#S >= low#S && idx#S < upp#S && elem#S = arr[idx#S] =>
///       invariant for elem#S
///
/// where the invariant can be computed in any existing domain. At the moment,
/// we support the interval and the heap domains.
///
/// After the invariants are computed, they are projected onto all read
/// indices (obtained from the array index analysis). There are two
/// approaches to the binding:
/// - adding equality between idx#S and a read index if there is a single
///   read index for the given array or
/// - copying the invariant for each read index and replacing idx#S by the
///   read index otherwise.
/// The projection must be done during invariant inference, too, to have the
/// context in which the invariant is solved.

class array_domaint : public domaint
{
public:
  array_domaint(unsigned int domain_number,
                replace_mapt &renaming_map,
                replace_mapt &init_renaming_map,
                const var_specst &var_specs,
                const local_SSAt &SSA,
                incremental_solvert *solver,
                template_generator_baset &template_generator);

  struct array_segmentt
  {
    var_spect array_spec; // array var spec
    vart elem_var;     // variable representing an array element of this segment
    vart index_var;    // index variable of this segment
    exprt lower_bound; // lower segment index
    exprt upper_bound; // upper segment index
    exprt array_size;

    array_segmentt(const var_spect &array_spec,
                   const vart &elem_var,
                   const vart &index_var,
                   const exprt &lower_bound,
                   const exprt &upper_bound,
                   const exprt &array_size)
      : array_spec(array_spec),
        elem_var(elem_var),
        index_var(index_var),
        lower_bound(lower_bound),
        upper_bound(upper_bound),
        array_size(array_size)
    {
    }

    exprt get_constraint();
  };
  std::map<vart, std::vector<array_segmentt>> segmentation_map;

  // Abstract domain for array elements
  std::unique_ptr<domaint> inner_domain;

  struct array_valuet : valuet
  {
    std::unique_ptr<valuet> inner_value;

    explicit array_valuet(std::unique_ptr<valuet> inner_value)
      : inner_value(std::move(inner_value))
    {
    }

    array_valuet *clone() override
    {
      return new array_valuet(std::unique_ptr<valuet>(inner_value->clone()));
    }
  };

  std::unique_ptr<domaint::valuet> new_value() override
  {
    return std::unique_ptr<valuet>(new array_valuet(inner_domain->new_value()));
  }

  void initialize_value(domaint::valuet &value) override;

  void project_on_vars(domaint::valuet &base_value,
                       const var_sett &vars,
                       exprt &result,
                       bool ignore_top) override;

  exprt segment_elem_equality();
  exprt map_value_to_read_indices(const array_valuet &value);

  void output_domain(std::ostream &out, const namespacet &ns) const override;
  void output_value(std::ostream &out,
                    const valuet &value,
                    const namespacet &ns) const override;
  void restrict_to_sympath(const symbolic_patht &sympath) override;
  void eliminate_sympaths(const std::vector<symbolic_patht> &sympaths) override;
  void undo_sympath_restriction() override;
  void remove_all_sympath_restrictions() override;

  tpolyhedra_domaint *get_tpolyhedra_domain() override
  {
    return inner_domain->get_tpolyhedra_domain();
  }

  std::unique_ptr<strategy_solver_baset>
  new_strategy_solver(incremental_solvert &solver,
                      const local_SSAt &SSA,
                      message_handlert &message_handler) override;

protected:
  void make_segments(const var_specst &var_specs, const namespacet &ns);
  void add_segment(const var_spect &var_spec,
                   const exprt &lower,
                   const exprt &upper);
  var_specst var_specs_from_segments();
  bool order_indices(var_listt &indices, const exprt &array_size);
  bool ordered_indices(const exprt &first,
                       const exprt &second,
                       const exprt &array_size);

  void extend_indices_by_loop_inits(var_listt &indices);
  void clear_non_lb_renamings();

  exprt get_array_size(const var_spect &array_spec);

  const local_SSAt &SSA;
  incremental_solvert *solver;

  // Renaming loop-back -> pre-loop
  replace_mapt &init_renaming_map;
  // A helper set to know which segment borders are pre-loop variants of
  // loop-back borders.
  std::set<exprt> loop_init_segment_borders;

  static unsigned segment_cnt;
};

#endif // CPROVER_2LS_DOMAINS_ARRAY_DOMAIN_H
