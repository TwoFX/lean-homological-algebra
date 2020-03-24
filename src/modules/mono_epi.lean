/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import linear_algebra.basic
import algebra.category.Module.basic
import modules.to_mathlib

section linear_map
universes u u' u''
variables {R : Type u} [ring R]
variables {M : Type u'} [add_comm_group M] [module R M]
variables {N : Type u''} [add_comm_group N] [module R N]

open linear_map
variables (f : M →ₗ[R] N)

lemma ker_comp : f.comp (f.ker).subtype = 0 :=
linear_map.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

lemma comp_mkq : f.range.mkq.comp f = 0 :=
linear_map.ext $ λ x, by simp; use x

lemma ker_eq_bot_of_cancel (h : ∀ (u v : f.ker →ₗ[R] M), f.comp u = f.comp v → u = v) :
  f.ker = ⊥ :=
begin
  have h₁ : f.comp (0 : f.ker →ₗ[R] M) = 0 := by ext; simp,
  have h₂ : f.comp f.ker.subtype = 0 := ker_comp f,
  rw [←submodule.range_subtype f.ker, ←h 0 f.ker.subtype (eq.trans h₁ h₂.symm)],
  exact submodule.map_zero ⊤
end

lemma range_eq_top_of_cancel
  (h : ∀ (u v : N →ₗ[R] f.range.quotient), u.comp f = v.comp f → u = v) : f.range = ⊤ :=
begin
  have h₁ : (0 : N →ₗ[R] f.range.quotient).comp f = 0 := by ext; simp,
  have h₂ : f.range.mkq.comp f = 0 := comp_mkq f,
  rw [←submodule.ker_mkq f.range, ←h 0 f.range.mkq (eq.trans h₁ h₂.symm)],
  exact ker_zero
end

end linear_map

section category
universes u

variables {R : Type u} [ring R]
variables {M N : Module R}

open category_theory Module

section

variables {A : Type u} {B : Type u} [add_comm_group A] [add_comm_group B] [module R A] [module R B]

def up (g : A →ₗ[R] B) : (of R A) ⟶ (of R B) := g

end

section
variables {A B : Module R}

def up_equiv (g : A ≃ₗ[R] B) : A ≅ B :=
{ hom := g,
  inv := g.symm,
  hom_inv_id' := linear_map.ext $ λ x, by erw [linear_equiv.symm_apply_apply, id_apply],
  inv_hom_id' := linear_map.ext $ λ x, by erw [linear_equiv.apply_symm_apply, id_apply] }

end

variables (f : M ⟶ N)

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
ker_eq_bot_of_cancel _ $ λ u v h, (@cancel_mono _ _ _ _ _ f _ (up u) (up v)).1 h

lemma ker_eq_bot_of_mono' (h : mono f) : f.ker = ⊥ :=
ker_eq_bot_of_mono f

lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
range_eq_top_of_cancel _ $ λ u v h, (@cancel_epi _ _ _ _ _ f _ (up u) (up v)).1 h

lemma mono_of_ker_eq_bot (hf : f.ker = ⊥) : mono f :=
⟨λ Z u v h, begin
  ext,
  apply (linear_map.ker_eq_bot.1 hf),
  rw [←linear_map.comp_apply, ←linear_map.comp_apply],
  apply linear_map.congr,
  exact h
end⟩

lemma epi_of_range_eq_top (hf : f.range = ⊤) : epi f :=
⟨λ Z u v h, begin
  ext,
  cases linear_map.range_eq_top.1 hf x with y hy,
  rw [←hy, ←linear_map.comp_apply, ←linear_map.comp_apply],
  apply linear_map.congr,
  exact h
end⟩

end category
