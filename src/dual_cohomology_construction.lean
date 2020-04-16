/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import abelian
import exact
import pseudoelements

/-!
The construction used by mathlib to define homology is as follows: Find a map
`im_to_ker : image (C.d i) ⟶ kernel (C.d (i + 1))` and set `H^i := coker im_to_ker`.

However, we could also use the dual construction: Find a map
`coker_to_coim : cokernel (C.d i) ⟶ coimage (C.d i)` and set `H'^i := ker coker_to_coim`.

In this file, we show that these two constructions yield isomorphic cohomology objects. This result
is needed in the construction of the LES in cohomology via the snake lemma.
-/

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

open pseudoelements

section
variables {V : Type u} [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

variables {A B C : V} {f : A ⟶ B} {g : B ⟶ C} (h : f ≫ g = 0)
include h

def im_to_ker : kernel (cokernel.π f) ⟶ kernel g :=
kernel.lift g (kernel.ι (cokernel.π f)) $
begin
  apply (preadditive.cancel_zero_iff_epi (factor_thru_image f)).1 (by apply_instance),
  rw ←category.assoc,
  rw image.fac,
  exact h,
end

def H := cokernel (im_to_ker h)

def coker_to_coim : cokernel f ⟶ cokernel (kernel.ι g) :=
cokernel.desc f (cokernel.π (kernel.ι g)) $
begin
  apply (preadditive.cancel_zero_iff_mono (factor_thru_coimage g)).1 (by apply_instance),
  rw category.assoc,
  rw coimage.fac,
  exact h,
end

def H' := kernel (coker_to_coim h)

def H_to_coker : (H h) ⟶ cokernel f :=
cokernel.desc (im_to_ker h) (kernel.ι g ≫ cokernel.π f)
begin
  rw ←category.assoc,
  erw limit.lift_π,
  erw kernel.condition,
end

def H_to_H' : H h ⟶ H' h :=
kernel.lift (coker_to_coim h) (H_to_coker h)
begin
  apply (preadditive.cancel_zero_iff_epi (cokernel.π (im_to_ker h))).1 (by apply_instance),
  rw ←category.assoc,
  erw colimit.ι_desc,
  dsimp,
  rw category.assoc,
  erw colimit.ι_desc,
  erw cokernel.condition,
end

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun

def ker_to_H' : kernel g ⟶ H' h :=
kernel.lift (coker_to_coim h) (kernel.ι g ≫ cokernel.π f)
begin
  rw category.assoc,
  erw colimit.ι_desc,
  erw cokernel.condition,
end

def H_to_H'_other : H h ⟶ H' h :=
cokernel.desc (im_to_ker h) (ker_to_H' h)
begin
  apply (preadditive.cancel_zero_iff_mono (kernel.ι (coker_to_coim h))).1 (by apply_instance),
  rw category.assoc,
  erw limit.lift_π,
  dsimp,
  rw ←category.assoc,
  erw limit.lift_π,
  erw kernel.condition,
end

lemma H_to_H'_eq_H_to_H'_other : H_to_H' h = H_to_H'_other h :=
begin
  apply (cancel_mono (kernel.ι (coker_to_coim h))).1,
  apply (cancel_epi (cokernel.π (im_to_ker h))).1,
  erw limit.lift_π,
  dsimp,
  erw colimit.ι_desc,
  dsimp,
  rw ←category.assoc,
  erw colimit.ι_desc,
  dsimp,
  erw limit.lift_π,
  refl,
end

instance H_to_H'_epi : epi (H_to_H' h) :=
begin
  rw H_to_H'_eq_H_to_H'_other,
  apply epi_of_pseudo_surjective,
  intro x,
  let y := (kernel.ι (coker_to_coim h) : _ ⟶ _) x,
  obtain ⟨z, hz⟩ := pseudo_surjective_of_epi (cokernel.π f) y,
  have : cokernel.π f ≫ coker_to_coim h = cokernel.π (kernel.ι g),
  { erw colimit.ι_desc, refl, },
  have : (cokernel.π (kernel.ι g) : _ ⟶ _) z = 0,
  { erw [←this, comp_apply, hz, ←comp_apply, kernel.condition, zero_apply], },
  obtain ⟨a, ha⟩ := (pseudo_exact_of_exact (cokernel_exact _)).2 _ this,
  use (cokernel.π (im_to_ker h) : _ ⟶ _) a,
  erw [←comp_apply, colimit.ι_desc],
  dsimp,
  apply pseudo_injective_of_mono (kernel.ι (coker_to_coim h)),
  erw [←comp_apply, limit.lift_π],
  dsimp,
  rw [comp_apply, ha, hz],
end

instance H_to_H'_mono : mono (H_to_H' h) :=
begin
  apply mono_of_zero_of_map_zero,
  intros a ha,
  obtain ⟨b, hb⟩ := pseudo_surjective_of_epi (cokernel.π (im_to_ker h)) a,
  let c := (kernel.ι g : _ ⟶ _) b,
  suffices : (cokernel.π f : _ ⟶ _) c = 0,
  { obtain ⟨d, hd⟩ := (pseudo_exact_of_exact (kernel_exact _)).2 _ this,
    have hc : c = (kernel.ι g : _ ⟶ _) b := rfl,
    rw ←hb,
    have : (im_to_ker h) d = b,
    { apply pseudo_injective_of_mono (kernel.ι g) _,
      rw ←comp_apply,
      erw limit.lift_π,
      dsimp,
      rw [hd, hc], },
    rw [←this, ←comp_apply, cokernel.condition, zero_apply] },
  have : (kernel.ι (coker_to_coim h) : _ ⟶ _) ((H_to_H' h) a) = 0,
  { erw [ha, apply_zero], },
  conv_lhs at this { erw [←comp_apply, limit.lift_π], dsimp,
    erw [←hb, ←comp_apply, colimit.ι_desc], dsimp,
    rw comp_apply },
  exact this,
end

instance H_to_H'_iso : is_iso (H_to_H' h) :=
mono_epi_iso _

def H_iso_H' : H h ≅ H' h :=
as_iso $ H_to_H' h

end

end category_theory.abelian
