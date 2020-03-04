import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.finite_limits

namespace category_theory.limits

attribute [derive decidable_eq] walking_parallel_pair_hom

section

local attribute [tidy] tactic.case_bash

instance (j j' : walking_parallel_pair) : fintype (walking_parallel_pair_hom.{v} j j') :=
{ elems := walking_parallel_pair.rec_on j
    (walking_parallel_pair.rec_on j'
      [walking_parallel_pair_hom.id walking_parallel_pair.zero].to_finset
      [walking_parallel_pair_hom.left, walking_parallel_pair_hom.right].to_finset)
    (walking_parallel_pair.rec_on j' ∅
      [walking_parallel_pair_hom.id walking_parallel_pair.one].to_finset),
  complete := by tidy }

end

instance : fin_category.{v} walking_parallel_pair.{v} := { }

end category_theory.limits