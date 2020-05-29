/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.category
import category_theory.limits.shapes.images
import category_theory.abelian.basic

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables {X Y : C} (f : X ⟶ Y)

section

variables {P Q : C} {u : X ⟶ P} {v : Y ⟶ Q}
variables {I : C} {f₁ : X ⟶ I} {f₂ : I ⟶ Y} [epi f₁] [mono f₂]
variables {I' : C} {g₁ : P ⟶ I'} {g₂ : I' ⟶ Q} [epi g₁] [mono g₂]
variables (h : u ≫ (g₁ ≫ g₂) = (f₁ ≫ f₂) ≫ v)

def upper : strong_epi_mono_factorisation (f₁ ≫ f₂) :=
{ I := I,
  e := f₁,
  m := f₂,
  fac' := rfl,
  e_strong_epi := strong_epi_of_epi _,
  m_mono := by apply_instance }

def lower : strong_epi_mono_factorisation (g₁ ≫ g₂) :=
{ I := I',
  e := g₁,
  m := g₂,
  fac' := rfl,
  e_strong_epi := strong_epi_of_epi _,
  m_mono := by apply_instance }

def diag_lift : I ⟶ I' := is_image.lift upper.to_mono_is_image (image.mono_factorisation (f₁ ≫ f₂)) ≫
  image.map (arrow.hom_mk' h) ≫ image.lift lower.to_mono_factorisation

lemma diag_lift_fac_left : f₁ ≫ (diag_lift h) = u ≫ g₁ :=
begin
  unfold diag_lift,
  slice_lhs 1 2 { erw is_image.fac_lift upper.to_mono_is_image (image.mono_factorisation (f₁ ≫ f₂)), },
  slice_lhs 1 2 { erw image.factor_map (arrow.hom_mk' h), },
  slice_lhs 2 3 { erw is_image.fac_lift, },
  refl
end

lemma diag_lift_fac_right : (diag_lift h) ≫ g₂ = f₂ ≫ v :=
begin
  -- watch this
  apply (cancel_epi f₁).1,
  slice_lhs 1 2 { rw diag_lift_fac_left h, },
  rw [category.assoc, h, category.assoc]
end

end

end category_theory.abelian
