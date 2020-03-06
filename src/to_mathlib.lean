import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.finite_limits

universes v u

namespace category_theory.limits

attribute [derive decidable_eq] walking_parallel_pair_hom
attribute [derive decidable_eq] walking_cospan.hom


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

instance fintype_walking_cospan_hom (j j' : walking_cospan) : fintype (walking_cospan.hom j j') :=
{ elems := walking_cospan.rec_on j
    (walking_cospan.rec_on j' [walking_cospan.hom.id walking_cospan.left].to_finset ∅ [walking_cospan.hom.inl].to_finset)
    (walking_cospan.rec_on j' ∅ [walking_cospan.hom.id walking_cospan.right].to_finset [walking_cospan.hom.inr].to_finset)
    (walking_cospan.rec_on j' ∅ ∅ [walking_cospan.hom.id walking_cospan.one].to_finset),
  complete := by tidy }

end

instance fin_category_walking_cospan : fin_category.{v} walking_cospan.{v} :=
{ fintype_hom := limits.fintype_walking_cospan_hom }
instance : fin_category.{v} walking_parallel_pair.{v} := { }

end category_theory.limits