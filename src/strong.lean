
/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import category_theory.limits.shapes.regular_mono
import hom_to_mathlib

open category_theory
open category_theory.limits

universes v u

namespace category_theory.lifting
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

structure lifting_problem :=
{P Q X Y : C}
{f : P ⟶ Q}
{u : P ⟶ X}
{v : Q ⟶ Y}
{z : X ⟶ Y}
[f_epi : epi f]
[z_mono : mono z]
(h : f ≫ v = u ≫ z)

attribute [instance] lifting_problem.f_epi
attribute [instance] lifting_problem.z_mono

variables {C}

def lifting_problem.mk' {P Q X Y : C} {f : P ⟶ Q} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y}
  (h : f ≫ v = u ≫ z) (f_epi : epi f) (z_mono : mono z) : lifting_problem.{v} C :=
by exactI lifting_problem.mk h

class has_solution (p : lifting_problem.{v} C) :=
(lift : p.Q ⟶ p.X)
(fac_left : p.f ≫ lift = p.u)
(fac_right : lift ≫ p.z = p.v)

abbreviation lift (p : lifting_problem.{v} C) [has_solution p] : p.Q ⟶ p.X := has_solution.lift p

section
local attribute [ext] has_solution

instance (p : lifting_problem.{v} C) : subsingleton (has_solution p) :=
subsingleton.intro $ λ a b,
begin
  ext,
  apply (cancel_epi p.f).1,
  simp only [has_solution.fac_left]
end

end

variables {P Q : C} (f : P ⟶ Q)

class strong_epi :=
(epi : epi f)
(has_solution : Π {X Y : C} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y} [mono.{v} z] (h : f ≫ v = u ≫ z),
  has_solution.{v}
  { P := P,
    Q := Q,
    X := X,
    Y := Y,
    f := f,
    u := u,
    v := v,
    z := z,
    f_epi := by apply_instance,
    z_mono := by apply_instance,
    h := h })

attribute [instance] strong_epi.has_solution

@[priority 100]
instance [strong_epi f] : epi f := strong_epi.epi f

section
variables {R : C} (g : Q ⟶ R) [epi f] [epi g]

instance [strong_epi f] [strong_epi g] : strong_epi (f ≫ g) :=
{ epi := by apply_instance,
  has_solution :=
  begin
    intros,
    have h₀ : f ≫ g ≫ v = u ≫ z, by simpa [category.assoc] using h,
    resetI,
    let w : Q ⟶ X := lift (lifting_problem.mk h₀),
    have h₁ : g ≫ v = w ≫ z,
    { rw has_solution.fac_right, },
    let t : R ⟶ X := lift (lifting_problem.mk h₁),
    refine ⟨t, _, _⟩,
    { rw category.assoc,
      rw has_solution.fac_left (lifting_problem.mk h₁),
      rw has_solution.fac_left (lifting_problem.mk h₀), },
    { rw has_solution.fac_right (lifting_problem.mk h₁), }
  end }

end

section
variables {R : C} (g : Q ⟶ R) [epi (f ≫ g)]

def strong_epi_of_strong_epi_comp [strong_epi (f ≫ g)] : strong_epi g :=
{ epi := epi_of_epi f g,
  has_solution :=
  begin
    intros,
    have : (f ≫ g) ≫ v = (f ≫ u) ≫ z,
    { simp only [category.assoc, h], },
    resetI,
    let t : R ⟶ X := lift (lifting_problem.mk this),
    refine ⟨t, _, _⟩,
    { apply (cancel_mono z).1,
      rw category.assoc,
      rw has_solution.fac_right,
      exact h, },
    { rw has_solution.fac_right, }
  end }

end

def mono_strong_epi_is_iso [strong_epi f] [mono f] : is_iso f :=
begin
  have : f ≫ 𝟙 Q = 𝟙 P ≫ f,
  { simp only [category.comp_id, category.id_comp], },
  haveI := strong_epi.epi f,
  let r : Q ⟶ P := lift (lifting_problem.mk this),
  refine ⟨r, _, _⟩,
  { rw auto_param_eq, rw has_solution.fac_left (lifting_problem.mk this), },
  { rw auto_param_eq, rw has_solution.fac_right (lifting_problem.mk this), }
end

instance strong_epi_of_regular_epi [regular_epi f] : strong_epi f :=
{ epi := by apply_instance,
  has_solution :=
  begin
    introsI,
    have : regular_epi.left f ≫ u = regular_epi.right f ≫ u,
    { apply (cancel_mono z).1,
      rw category.assoc,
      rw ←h,
      rw ←category.assoc,
      rw regular_epi.w f,
      rw category.assoc,
      rw h,
      rw category.assoc, },
    obtain ⟨t, ht⟩ := colimit_cofork.desc' _ _ (regular_epi.is_colimit f) _ this,
    refine ⟨t, ht, _⟩,
    apply (cancel_epi f).1,
    rw ←category.assoc,
    erw ht,
    rw ←h,
  end }

end category_theory.lifting
