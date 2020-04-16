/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import abelian
import exact
import hom_to_mathlib
import pseudoelements
import tactic.diagram_chase

open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.abelian.pseudoelements

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun

universes v u
section
variables {V : Type u} [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

section four
variables {A B C D A' B' C' D' : V}
variables {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}
variables (fg : exact f g) (gh : exact g h) (fg' : exact f' g') (gh' : exact g' h')
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include fg gh fg' gh' comm₁ comm₂ comm₃

lemma four (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
mono_of_zero_of_map_zero _ $ assume (c : C) (hc : γ c = 0), show c = 0, from

  have h c = 0, from
    suffices δ (h c) = 0, from zero_of_map_zero _ (pseudo_injective_of_mono _) _ this,
    calc δ (h c) = h' (γ c) : by rw [←comp_apply, ←comm₃, comp_apply]
             ... = h' 0     : by rw hc
             ... = 0        : apply_zero _,

  exists.elim ((pseudo_exact_of_exact gh).2 _ this) $ assume (b : B) (hb : g b = c),
    have g' (β b) = 0, from
      calc g' (β b) = γ (g b) : by rw [←comp_apply, comm₂, comp_apply]
                ... = γ c     : by rw hb
                ... = 0       : hc,

    exists.elim ((pseudo_exact_of_exact fg').2 _ this) $ assume (a' : A') (ha' : f' a' = β b),
      exists.elim (pseudo_surjective_of_epi α a') $ assume (a : A) (ha : α a = a'),

      have f a = b, from
        suffices β (f a) = β b, from pseudo_injective_of_mono _ this,
        calc β (f a) = f' (α a) : by rw [←comp_apply, ←comm₁, comp_apply]
                 ... = f' a'    : by rw ha
                 ... = β b      : ha',

      calc c = g b     : hb.symm
         ... = g (f a) : by rw this
         ... = 0       : (pseudo_exact_of_exact fg).1 _

lemma four' [epi α] [mono β] [mono δ] : mono γ :=
mono_of_zero_of_map_zero _ $ λ c hc,
begin
  chase c using [g, β, f', α] with b b' a' a,
  have : f a = b, by commutativity,
  commutativity
end

end four

section kernels
variables {P Q R P' Q' R' : V}
variables {f : P ⟶ Q} {g : Q ⟶ R} {f' : P' ⟶ Q'} {g' : Q' ⟶ R'}
variables {α : P ⟶ P'} {β : Q ⟶ Q'} {γ : R ⟶ R'}
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ)
variables (fg : exact f g) (fg' : exact f' g')
variables [mono f']

include comm₁ comm₂ fg fg'

lemma kernels' : ∃! (u : kernel α ⟶ kernel β) (v : kernel β ⟶ kernel γ),
  (kernel.ι α ≫ f = u ≫ kernel.ι β) ∧ (kernel.ι β ≫ g = v ≫ kernel.ι γ)
  ∧ exact u v :=
begin
  obtain ⟨u, hu₁, hu₂⟩ := kernel.lift'' β (kernel.ι α ≫ f) (begin
    rw category.assoc, rw ←comm₁, rw ←category.assoc,
    rw kernel.condition, rw has_zero_morphisms.zero_comp,
  end),
  obtain ⟨v, hv₁, hv₂⟩ := kernel.lift'' γ (kernel.ι β ≫ g) (begin
    rw category.assoc, rw ←comm₂, rw ←category.assoc,
    rw kernel.condition, rw has_zero_morphisms.zero_comp,
  end),

  refine ⟨u, ⟨v, ⟨hu₁.symm, hv₁.symm, exact_of_pseudo_exact _ _ ⟨_, _⟩⟩,
    λ v', by rintro ⟨_, h, _⟩; exact hv₂ _ h.symm⟩,
    λ u', by rintro ⟨_, ⟨h, _⟩, _⟩; exact hu₂ _ h.symm⟩,

  { intro a,
    apply zero_of_map_zero _ (pseudo_injective_of_mono (kernel.ι γ)),
    calc (kernel.ι γ : kernel γ ⟶ R) (v (u a))
          = (u ≫ v ≫ kernel.ι γ) a : by rw [←comp_apply, ←comp_apply]
      ... = (u ≫ kernel.ι β ≫ g) a : by rw hv₁
      ... = (kernel.ι α ≫ f ≫ g) a : by rw [←category.assoc, hu₁, category.assoc]
      ... = (kernel.ι α ≫ 0 : kernel α ⟶ R) a : by rw fg.1
      ... = 0 : by rw [has_zero_morphisms.comp_zero, zero_apply] },
  { intros b hb,

    have : g ((kernel.ι β : kernel β ⟶ Q) b) = 0,
    calc g ((kernel.ι β : kernel β ⟶ Q) b)
          = (kernel.ι γ : kernel γ ⟶ R) (v b) : by rw [←comp_apply, ←hv₁, comp_apply]
      ... = (kernel.ι γ : kernel γ ⟶ R) 0 : by rw hb
      ... = 0 : apply_zero _,

    obtain ⟨a', ha'⟩ := (pseudo_exact_of_exact fg).2 _ this,

    have : α a' = 0,
    { apply zero_of_map_zero _ (pseudo_injective_of_mono f'),
      calc f' (α a') = β (f a') : by rw [←comp_apply, comm₁, comp_apply]
      ... = β ((kernel.ι β : kernel β ⟶ Q) b) : by rw ha'
      ... = 0 : (pseudo_exact_of_exact (kernel_exact β)).1 _ },

    obtain ⟨a, ha⟩ := (pseudo_exact_of_exact (kernel_exact α)).2 _ this,

    use a,

    apply pseudo_injective_of_mono (kernel.ι β),
    calc (kernel.ι β : kernel β → Q) (u a)
          = f ((kernel.ι α : kernel α ⟶ P) a) : by rw [←comp_apply, hu₁, comp_apply]
      ... = f a' : by rw ha
      ... = (kernel.ι β : kernel β ⟶ Q) b : ha' }
end

end kernels

end

namespace kernels_full
variables {V : Type u} [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

variables {A B C D E F G H I : V}
variables {γ : A ⟶ D} {δ : B ⟶ E} {ε : C ⟶ F} {θ : D ⟶ G} {l : E ⟶ H} {μ : F ⟶ I}
variables {ζ : D ⟶ E} {η : E ⟶ F} {ν : G ⟶ H} {ξ : H ⟶ I}
variables (comm₁ : ζ ≫ l = θ ≫ ν) (comm₂ : η ≫ μ = l ≫ ξ)
variables (γθ : exact γ θ) (δl : exact δ l) (εμ : exact ε μ)
variables (ζη : exact ζ η) (νξ : exact ν ξ)
include comm₁ comm₂ γθ δl εμ ζη νξ

def fill_left [mono δ] : { x : A ⟶ B // x ≫ δ = γ ≫ ζ } :=
kernel_fork.is_limit.lift' (kernel_of_mono_exact _ _ δl) (γ ≫ ζ) $
  by rw [category.assoc, comm₁, ←category.assoc, γθ.1, has_zero_morphisms.zero_comp]

def fill_right [mono ε] : { x : B ⟶ C // x ≫ ε = δ ≫ η } :=
kernel_fork.is_limit.lift' (kernel_of_mono_exact _ _ εμ) (δ ≫ η) $
  by rw [category.assoc, comm₂, ←category.assoc, δl.1, has_zero_morphisms.zero_comp]

variables {α : A ⟶ B} {β : B ⟶ C}
variables (comm₃ : α ≫ δ = γ ≫ ζ) (comm₄ : β ≫ ε = δ ≫ η)
include comm₃ comm₄

lemma fill_left_unique [mono δ] : α = fill_left comm₁ comm₂ γθ δl εμ ζη νξ :=
begin
  apply (kernel_of_mono_exact _ _ δl).hom_ext,
  intro j,
  cases j,
  { erw (fill_left comm₁ comm₂ γθ δl εμ ζη νξ).2,
    erw comm₃ },
  { simp only [kernel_fork.app_one],
    erw has_zero_morphisms.comp_zero,
    erw has_zero_morphisms.comp_zero }
end

lemma fill_right_unique [mono ε] : β = fill_right comm₁ comm₂ γθ δl εμ ζη νξ :=
begin
  apply (kernel_of_mono_exact _ _ εμ).hom_ext,
  intro j,
  cases j,
  { erw (fill_right comm₁ comm₂ γθ δl εμ ζη νξ).2,
    erw comm₄ },
  { simp only [kernel_fork.app_one],
    erw has_zero_morphisms.comp_zero,
    erw has_zero_morphisms.comp_zero }
end

lemma kernels [mono δ] [mono ε] [mono ν] : exact α β :=
begin
  apply exact_of_pseudo_exact,
  split,
  { intro a,
    commutativity },
  { intros b hb,
    chase b using [δ, ζ, γ] with e d a,
    exact ⟨a, by commutativity⟩ }
end

lemma kernels' [mono δ] [mono ε] [mono ν] : exact α β :=
begin
  apply exact_of_pseudo_exact,
  split,

  { intro a,
    apply zero_of_map_zero _ (pseudo_injective_of_mono ε),
    calc ε (β (α a)) = (α ≫ β ≫ ε) a : by rw [←comp_apply, ←comp_apply]
      ... = (α ≫ δ ≫ η) a : by rw comm₄
      ... = (γ ≫ ζ ≫ η) a : by rw [←category.assoc, comm₃, category.assoc]
      ... = (γ ≫ (0 : D ⟶ F)) a : by rw ζη.1
      ... = 0 : by rw [has_zero_morphisms.comp_zero, zero_apply] },

  { intros b hb,

    have : η (δ b) = 0,
    calc η (δ b) = ε (β b) : by rw [←comp_apply, ←comm₄, comp_apply]
      ... = ε 0 : by rw hb
      ... = 0 : apply_zero _,

    obtain ⟨d, hd⟩ := (pseudo_exact_of_exact ζη).2 _ this,

    have : θ d = 0,
    { apply zero_of_map_zero _ (pseudo_injective_of_mono ν),
      calc ν (θ d) = l (ζ d) : by rw [←comp_apply, ←comm₁, comp_apply]
        ... = l (δ b) : by rw hd
        ... = 0 : (pseudo_exact_of_exact δl).1 _ },

    obtain ⟨a, ha⟩ := (pseudo_exact_of_exact γθ).2 _ this,

    use a,

    apply pseudo_injective_of_mono δ,
    calc δ (α a) = ζ (γ a) : by rw [←comp_apply, comm₃, comp_apply]
      ... = ζ d : by rw ha
      ... = δ b : hd }
end

end kernels_full
