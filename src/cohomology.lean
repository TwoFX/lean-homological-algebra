/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import abelian
import exact
import pseudoelements

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

open pseudoelements

section
variables (A : Type u) [𝒜 : category.{v} A] [abelian.{v} A]
include 𝒜

local attribute [instance] has_zero_object.has_zero

structure cochain_complex :=
(M : Π (n : ℤ), A)
(d : Π (n : ℤ), M n ⟶ M (n + 1))
(condition : ∀ (n : ℤ), (d n) ≫ (d (n + 1)) = 0)

variables {A}

/-- Shifted! -/
def im_to_ker (C : cochain_complex.{v} A) (n : ℤ) :
    kernel (cokernel.π (C.d n)) ⟶ kernel (C.d (n + 1)) :=
kernel.lift (C.d (n + 1)) (kernel.ι (cokernel.π (C.d n)))
begin
  apply (preadditive.cancel_zero_iff_epi _).1
    (show epi (factor_thru_image (C.d n)), by apply_instance),
  rw [←category.assoc, image.fac _],
  exact C.condition _
end


abbreviation cohomology (C : cochain_complex.{v} A) (n : ℤ) : A :=
cokernel $ im_to_ker C (n - 1)

lemma zero_from_exact (C : cochain_complex.{v} A) (n : ℤ)
  (e : exact (C.d n) (C.d (n + 1))) : (cohomology C (n + 1)) ≅ 0 :=
begin
  have : exact (C.d (n + 1 - 1)) (C.d ((n + 1 - 1) + 1)),
  { convert e;
    exact int.pred_succ n, },
  let i : kernel (cokernel.π (C.d (n + 1 - 1))) ≅ kernel (C.d ((n + 1 - 1) + 1)) :=
    functor.map_iso (cones.forget _)
    (is_limit.unique_up_to_iso (exact_ker _ _ this) (limit.is_limit _)),
  haveI is : is_iso (im_to_ker C (n + 1 - 1)) := is_iso.of_iso i,
  exact cokernel.of_epi.{v u} (im_to_ker C (n + 1 - 1)),
end

section

local attribute [instance] hom_to_fun
local attribute [instance] object_to_sort

lemma exact_from_zero (C : cochain_complex.{v} A) (n : ℤ)
  (i : cohomology C (n + 1) ≅ 0) : exact (C.d n) (C.d (n + 1)) :=
⟨C.condition n, begin
  -- This proof is stupid

  apply (zero_iff _).2,
  intro a,
  rw comp_apply,
  have : cokernel.π (im_to_ker C n) = 0,
  { rw ←category.comp_id _ (cokernel.π (im_to_ker C n)),
    have a := iso.hom_inv_id i,
    have : n = (n + 1 - 1),
    { simp, },
    rw this,
    rw ←a,
    rw has_zero_object.zero_of_from_zero i.inv,
    rw has_zero_morphisms.comp_zero,
    rw has_zero_morphisms.comp_zero, },
  have : (cokernel.π (im_to_ker C n) : kernel (C.d (n + 1)) ⟶ cokernel (im_to_ker C n)) a = 0,
  { rw this, rw zero_apply, },
  cases (pseudo_exact_of_exact (cokernel_exact (im_to_ker C n))).2 _ this with b hb,
  rw ←hb,
  rw ←comp_apply,
  rw ←comp_apply,
  rw ←category.assoc,
  erw limit.lift_π,
  erw kernel.condition,
  rw zero_apply,

  -- but it works
end⟩

end

end

end category_theory.abelian
