/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import abelian

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

def exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : Prop :=
f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0

def exact_fork {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (e : exact f g) : kernel_fork g :=
kernel_fork.of_ι (kernel.ι (cokernel.π f)) $
  (preadditive.cancel_zero_iff_epi (factor_thru_image f)).1
    (by apply_instance) _ (kernel.ι (cokernel.π f) ≫ g) $
    by rw [←category.assoc, image.fac f, e.1]

def exact_ker {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (e : exact f g) : is_limit $ exact_fork f g e :=
fork.is_limit.mk _
  (λ s, kernel.lift _ (fork.ι s)
  begin
    let t : s.X ⟶ kernel g := kernel.lift g (fork.ι s) (kernel_fork.condition _),
    have : t ≫ kernel.ι g = fork.ι s := by erw limit.lift_π; refl,
    rw [←this, category.assoc, e.2, has_zero_morphisms.comp_zero]
  end)
  (λ s, by erw limit.lift_π; refl)
  (λ s m h, by ext; erw [h walking_parallel_pair.zero, limit.lift_π]; refl)

def exact_cofork {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (e : exact f g) : cokernel_cofork f :=
cokernel_cofork.of_π (cokernel.π (kernel.ι g)) $
  (preadditive.cancel_zero_iff_mono (factor_thru_coimage g)).1
    (by apply_instance) _ (f ≫ cokernel.π (kernel.ι g)) $
    by rw [category.assoc, coimage.fac g, e.1]

def exact_coker {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (e : exact f g) :
  is_colimit $ exact_cofork f g e :=
cofork.is_colimit.mk _
  (λ s, cokernel.desc _ (cofork.π s)
  begin
    let t : cokernel f ⟶ s.X := cokernel.desc f (cofork.π s) (cokernel_cofork.condition _),
    have : cokernel.π f ≫ t = cofork.π s := by erw colimit.ι_desc; refl,
    rw [←this, ←category.assoc, e.2, has_zero_morphisms.zero_comp]
  end)
  (λ s, by erw colimit.ι_desc; refl)
  (λ s m h, by ext; erw [h walking_parallel_pair.one, colimit.ι_desc]; refl)

lemma exact_zero_of_mono (P : C) {Q R : C} (f : Q ⟶ R) [mono f] : exact (0 : P ⟶ Q) f :=
⟨has_zero_morphisms.zero_comp _ _ _,
begin
  rw (preadditive.cancel_zero_iff_mono f).1 (by apply_instance) _ (kernel.ι f) (kernel.condition _),
  exact has_zero_morphisms.zero_comp _ _ _,
end⟩

lemma mono_of_exact_zero (P : C) {Q R : C} (f : Q ⟶ R) (h : exact (0 : P ⟶ Q) f) : mono f :=
(preadditive.cancel_zero_iff_mono f).2 $ λ Z g h₀,
begin
  obtain ⟨k, hk⟩ := limit_kernel_fork.lift' f (exact_ker _ _ h) g h₀,
  have := (preadditive.cancel_zero_iff_epi (factor_thru_image (0 : P ⟶ Q))).1
    (by apply_instance) _ _ (image.fac (0 : P ⟶ Q)),
  change k ≫ kernel.ι (cokernel.π (0 : P ⟶ Q)) = g at hk,
  rw ←hk,
  conv_lhs { congr, skip, rw this },
  exact has_zero_morphisms.comp_zero _ _ _,
end

lemma exact_zero_of_epi {P Q : C} (f : P ⟶ Q) (R : C) [epi f] : exact f (0 : Q ⟶ R) :=
⟨has_zero_morphisms.comp_zero _ _ _,
begin
  rw (preadditive.cancel_zero_iff_epi f).1 (by apply_instance) _ (cokernel.π f) (cokernel.condition _),
  exact has_zero_morphisms.comp_zero _ _ _,
end⟩

lemma epi_of_exact_zero {P Q : C} (f : P ⟶ Q) (R : C) (h : exact f (0 : Q ⟶ R)) : epi f :=
(preadditive.cancel_zero_iff_epi f).2 $ λ Z g h₀,
begin
  obtain ⟨k, hk⟩ := cokernel.desc' f g h₀,
  haveI : is_iso (kernel.ι (0 : Q ⟶ R)) := kernel.ι_of_zero _ _,
  apply (preadditive.cancel_zero_iff_epi (kernel.ι (0 : Q ⟶ R))).1 (by apply_instance) _ _,
  rw [←hk, ←category.assoc, h.2],
  exact has_zero_morphisms.zero_comp _ _ _,
end

lemma kernel_exact {P Q : C} (f : P ⟶ Q) : exact (kernel.ι f) f :=
⟨kernel.condition _, cokernel.condition _⟩

lemma cokernel_exact {P Q : C} (f : P ⟶ Q) : exact f (cokernel.π f) :=
⟨cokernel.condition _, kernel.condition _⟩

def kernel_of_mono_exact {P Q R : C} (f : P ⟶ Q) [mono f] (g : Q ⟶ R) (h : exact f g) :
  is_limit $ kernel_fork.of_ι f h.1 :=
begin
  let I := kernel (cokernel.π f),
  let i : kernel g ≅ I := functor.map_iso (cones.forget _)
    (is_limit.unique_up_to_iso (limit.is_limit _) (exact_ker f g h)),
  have h₀ : i.hom ≫ kernel.ι (cokernel.π f) = kernel.ι g :=
    cone_morphism.w (is_limit.unique_up_to_iso (limit.is_limit _) (exact_ker f g h)).hom
      walking_parallel_pair.zero,
  haveI : mono (factor_thru_image f) := mono_of_mono_fac (image.fac f),
  haveI : is_iso (factor_thru_image f) := mono_epi_iso _,
  let j : P ≅ I := as_iso (factor_thru_image f),
  apply kernel.transport _ _ (j ≪≫ i.symm),
  erw [category.assoc, ←(iso.eq_inv_comp i).2 h₀, image.fac],
end

def cokernel_of_epi_exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) [epi g] (h : exact f g) :
  is_colimit $ cokernel_cofork.of_π g h.1 :=
begin
  let I := cokernel (kernel.ι g),
  let i : cokernel f ≅ I := functor.map_iso (cocones.forget _)
    (is_colimit.unique_up_to_iso (colimit.is_colimit _) (exact_coker f g h)),
  have h₀ : cokernel.π f ≫ i.hom = cokernel.π (kernel.ι g) :=
    cocone_morphism.w (is_colimit.unique_up_to_iso (colimit.is_colimit _) (exact_coker f g h)).hom
      walking_parallel_pair.one,
  haveI : epi (factor_thru_coimage g) := epi_of_epi_fac (coimage.fac g),
  haveI : is_iso (factor_thru_coimage g) := mono_epi_iso _,
  let j : I ≅ R := as_iso (factor_thru_coimage g),
  apply cokernel.transport' _ _ (i ≪≫ j),
  erw [←category.assoc, h₀, coimage.fac],
end

end

end category_theory.abelian
