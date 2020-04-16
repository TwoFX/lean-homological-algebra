/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import abelian
import exact
import pseudoelements
import algebra.homology.homology
import epi_mono
import abelian_SEMF

open category_theory
open category_theory.limits
open category_theory.epi_mono
open cochain_complex

universes v u

namespace category_theory.abelian

open pseudoelements

section
variables {V : Type u} [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

local attribute [instance] has_zero_object.has_zero

section
variable (C : cochain_complex.{v} V)

def cokernel_to_image_map (i : ℤ) : cokernel (C.d i) ⟶ image (C.d (i + 1)) :=
cokernel.desc (C.d i) (cokernel.π (kernel.ι (C.d (i + 1))))
begin
  apply (preadditive.cancel_zero_iff_mono (factor_thru_coimage (C.d (i + 1)))).1 (by apply_instance),
  rw [category.assoc, coimage.fac, d_squared],
end

instance coker_to_im_epi {i : ℤ} : epi (cokernel_to_image_map C i) :=
epi_of_epi_fac $ show cokernel.π (C.d i) ≫ cokernel_to_image_map C i = cokernel.π (kernel.ι (C.d (i + 1))),
  by erw colimit.ι_desc; refl

def dd (i : ℤ) : cokernel (C.d i) ⟶ kernel (C.d (i + 1 + 1)) :=
cokernel_to_image_map C i ≫ image_to_kernel_map C (i + 1)

lemma exact_right (i : ℤ) : exact (dd C i) (cokernel.π (image_to_kernel_map C (i + 1))) :=
exact_left_epi _ _ _ $ cokernel_exact _



end

section
variable (V)

-- Not a good way to define it
structure SES_of_cochain_complexes :=
(A B C : cochain_complex.{v} V)
(f : A ⟶ B)
(g : B ⟶ C)
[monos : ∀ i, mono (differential_object.hom.f f i)]
[epis : ∀ i, epi (g.f i)]
(exacts : ∀ i, exact (f.f i) (g.f i))

end


end

end category_theory.abelian
