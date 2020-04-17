/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import abelian
import abelian_SEMF

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
⟨has_zero_morphisms.zero_comp _ _,
begin
  rw (preadditive.cancel_zero_iff_mono f).1 (by apply_instance) _ (kernel.ι f) (kernel.condition _),
  exact has_zero_morphisms.zero_comp _ _
end⟩

lemma mono_of_exact_zero (P : C) {Q R : C} (f : Q ⟶ R) (h : exact (0 : P ⟶ Q) f) : mono f :=
(preadditive.cancel_zero_iff_mono f).2 $ λ Z g h₀,
begin
  obtain ⟨k, hk⟩ := kernel_fork.is_limit.lift' (exact_ker _ _ h) g h₀,
  have := (preadditive.cancel_zero_iff_epi (factor_thru_image (0 : P ⟶ Q))).1
    (by apply_instance) _ _ (image.fac (0 : P ⟶ Q)),
  change k ≫ kernel.ι (cokernel.π (0 : P ⟶ Q)) = g at hk,
  rw ←hk,
  conv_lhs { congr, skip, rw this },
  exact has_zero_morphisms.comp_zero _ _
end

lemma exact_zero_of_epi {P Q : C} (f : P ⟶ Q) (R : C) [epi f] : exact f (0 : Q ⟶ R) :=
⟨has_zero_morphisms.comp_zero _ _,
begin
  rw (preadditive.cancel_zero_iff_epi f).1 (by apply_instance) _ (cokernel.π f) (cokernel.condition _),
  exact has_zero_morphisms.comp_zero _ _
end⟩

lemma exact_zero_of_epi' {P Q : C} (f : P ⟶ Q) [epi f] : exact f (0 : Q ⟶ Q) :=
exact_zero_of_epi _ _

lemma epi_of_exact_zero {P Q : C} (f : P ⟶ Q) (R : C) (h : exact f (0 : Q ⟶ R)) : epi f :=
(preadditive.cancel_zero_iff_epi f).2 $ λ Z g h₀,
begin
  obtain ⟨k, hk⟩ := cokernel.desc' f g h₀,
  haveI : is_iso (kernel.ι (0 : Q ⟶ R)) := kernel.ι_of_zero _ _,
  apply (preadditive.cancel_zero_iff_epi (kernel.ι (0 : Q ⟶ R))).1 (by apply_instance) _ _,
  rw [←hk, ←category.assoc, h.2],
  exact has_zero_morphisms.zero_comp _ _
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
  apply cokernel.transport _ _ (i ≪≫ j),
  erw [←category.assoc, h₀, coimage.fac],
end

lemma image_exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (h : exact f g) :
  exact (kernel.ι (cokernel.π f)) g :=
⟨begin
  apply (preadditive.cancel_zero_iff_epi (factor_thru_image f)).1 (by apply_instance),
  rw ←category.assoc,
  rw image.fac f,
  exact h.1,
end,
begin
  obtain ⟨l, hl⟩ := cokernel.desc' f (cokernel.π (kernel.ι (cokernel.π f)))
    begin conv_lhs { congr, rw ←image.fac f, }, rw category.assoc, rw cokernel.condition,
      rw has_zero_morphisms.comp_zero, end,
  rw ←hl,
  rw ←category.assoc,
  rw h.2,
  rw has_zero_morphisms.zero_comp,
end⟩

lemma exact_image {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (h : exact f g) :
  exact f (factor_thru_image g) :=
⟨begin
  apply (preadditive.cancel_zero_iff_mono (kernel.ι (cokernel.π g))).1 (by apply_instance),
  rw category.assoc,
  rw image.fac g,
  exact h.1,
end,
begin
  obtain ⟨l, hl⟩ := kernel.lift' g (kernel.ι (factor_thru_image g))
    begin conv_lhs { congr, skip, rw ←image.fac g, }, rw ←category.assoc, rw kernel.condition,
      rw has_zero_morphisms.zero_comp, end,
  rw ←hl,
  rw category.assoc,
  rw h.2,
  rw has_zero_morphisms.comp_zero,
end⟩

lemma exact_iso {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) {Q' : C} (i : Q ≅ Q') (h : exact f g) :
  exact (f ≫ i.hom) (i.inv ≫ g) :=
⟨by simpa using h.1,
begin
  obtain ⟨l, hl⟩ := kernel.lift' g (kernel.ι (i.inv ≫ g) ≫ i.inv)
    (by rw [category.assoc, kernel.condition]),
  obtain ⟨m, hm⟩ := cokernel.desc' f (i.hom ≫ cokernel.π (f ≫ i.hom))
    (by rw [←category.assoc, cokernel.condition]),
  calc kernel.ι (i.inv ≫ g) ≫ cokernel.π (f ≫ i.hom)
        = kernel.ι (i.inv ≫ g) ≫ (i.inv ≫ i.hom) ≫ cokernel.π (f ≫ i.hom) : by rw [iso.inv_hom_id, category.id_comp]
    ... = (kernel.ι (i.inv ≫ g) ≫ i.inv) ≫ i.hom ≫ cokernel.π (f ≫ i.hom) : by simp only [category.assoc]
    ... = (l ≫ kernel.ι g) ≫ cokernel.π f ≫ m : by rw [←hl, ←hm]
    ... = l ≫ (kernel.ι g ≫ cokernel.π f) ≫ m : by simp only [category.assoc]
    ... = l ≫ 0 ≫ m : by rw h.2
    ... = 0 : by rw [has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero]
end⟩

lemma exact_iso_right {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) {R' : C} (i : R ≅ R') (h : exact f g) :
  exact f (g ≫ i.hom) :=
⟨by rw [←category.assoc, h.1, has_zero_morphisms.zero_comp],
begin
  obtain ⟨l, hl⟩ := kernel.lift' g (kernel.ι (g ≫ i.hom))
    (calc kernel.ι (g ≫ i.hom) ≫ g
          = kernel.ι (g ≫ i.hom) ≫ g ≫ i.hom ≫ i.inv : by simp
      ... = (kernel.ι (g ≫ i.hom) ≫ g ≫ i.hom) ≫ i.inv : by simp only [category.assoc]
      ... = 0 ≫ i.inv : by rw kernel.condition
      ... = 0 : by rw has_zero_morphisms.zero_comp),

  rw [←hl, category.assoc, h.2, has_zero_morphisms.comp_zero],
end⟩

lemma exact_iso_left {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) {P' : C} (i : P' ≅ P) (h : exact f g) :
  exact (i.hom ≫ f) g :=
⟨by rw [category.assoc, h.1, has_zero_morphisms.comp_zero],
begin
  obtain ⟨l, hl⟩ := cokernel.desc' f (cokernel.π (i.hom ≫ f))
    (calc f ≫ cokernel.π (i.hom ≫ f)
          = (i.inv ≫ i.hom) ≫ f ≫ cokernel.π (i.hom ≫ f) : by simp
      ... = i.inv ≫ (i.hom ≫ f) ≫ cokernel.π (i.hom ≫ f) : by simp only [category.assoc]
      ... = i.inv ≫ 0 : by rw cokernel.condition
      ... = 0 : by rw has_zero_morphisms.comp_zero),

  rw [←hl, ←category.assoc, h.2, has_zero_morphisms.zero_comp],
end⟩

lemma epi_mono_exact_left {P Q R S : C} (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S)
  (e : exact (f ≫ g) h) [epi f] [mono g] : exact g h :=
begin
  let upper : strong_epi_mono_factorisation (f ≫ g) :=
  { I := _, e := f, m := g, fac' := rfl,
    m_mono := by apply_instance, e_strong_epi := strong_epi_of_epi _ },
  let lower := image_SEMF (f ≫ g),
  let s : Q ≅ kernel (cokernel.π (f ≫ g)) := is_image.iso_ext upper.to_mono_is_image
    lower.to_mono_is_image,
  have : s.hom ≫ kernel.ι (cokernel.π (f ≫ g)) = g,
  { erw is_image.lift_fac },
  rw ←this,
  apply exact_iso_left _ _ s,
  exact image_exact _ _ e,
end

lemma epi_mono_exact_right {P Q R S : C} (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S)
  (e : exact f (g ≫ h)) [epi g] [mono h] : exact f g :=
begin
  let upper : strong_epi_mono_factorisation (g ≫ h) :=
  { I := _, e := g, m := h, fac' := rfl,
  m_mono := by apply_instance, e_strong_epi := strong_epi_of_epi _ },
  let lower := image_SEMF (g ≫ h),
  let s : kernel (cokernel.π (g ≫ h)) ≅ R := is_image.iso_ext lower.to_mono_is_image
    upper.to_mono_is_image,
  have : factor_thru_image (g ≫ h) ≫ s.hom = g,
  { erw is_image.fac_lift lower.to_mono_is_image upper.to_mono_factorisation },
  rw ←this,
  apply exact_iso_right _ _ s,
  exact exact_image _ _ e,
end

lemma exact_left_epi {P Q R S : C} (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S) (e : exact g h) [epi f] :
  exact (f ≫ g) h :=
⟨by rw [category.assoc, e.1, has_zero_morphisms.comp_zero],
begin
  obtain ⟨l, hl⟩ := cokernel.desc' g (cokernel.π (f ≫ g))
    begin
      apply (preadditive.cancel_zero_iff_epi f).1 (by apply_instance),
      rw [←category.assoc, cokernel.condition],
    end,
  rw [←hl, ←category.assoc, e.2, has_zero_morphisms.zero_comp],
end⟩


end

end category_theory.abelian
