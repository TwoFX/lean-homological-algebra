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

lemma abelian_four' (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
mono_of_zero_of_map_zero _ $ λ c hc,
begin
  have : h c = 0,
  { apply pseudo_injective_of_mono δ,
    rw ←comp_apply,
    rw ←comm₃,
    rw comp_apply,
    rw hc,
    rw apply_zero,
    rw apply_zero, },
  cases (pseudo_exact_of_exact gh).2 _ this with b hb,
  have : g' (β b) = 0,
  { rw ←comp_apply,
    rw comm₂,
    rw comp_apply,
    rw hb,
    exact hc, },
  cases (pseudo_exact_of_exact fg').2 _ this with a' ha',
  cases pseudo_surjective_of_epi α a' with a ha,
  have : f a = b,
  { apply pseudo_injective_of_mono β,
    rw ←comp_apply,
    rw ←comm₁,
    rw comp_apply,
    rw ha,
    exact ha', },
  rw ←hb,
  rw ←this,
  rw (pseudo_exact_of_exact fg).1,
end

lemma abelian_four'' (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
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

lemma kernels : ∃ (u : kernel α ⟶ kernel β) (v : kernel β ⟶ kernel γ),
  (kernel.ι α ≫ f = u ≫ kernel.ι β) ∧ (kernel.ι β ≫ g = v ≫ kernel.ι γ)
  ∧ exact u v :=
begin
  obtain ⟨u, hu⟩ := kernel.lift' β (kernel.ι α ≫ f) (begin
    rw category.assoc, rw ←comm₁, rw ←category.assoc,
    rw kernel.condition, rw has_zero_morphisms.zero_comp,
  end),
  obtain ⟨v, hv⟩ := kernel.lift' γ (kernel.ι β ≫ g) (begin
    rw category.assoc, rw ←comm₂, rw ←category.assoc,
    rw kernel.condition, rw has_zero_morphisms.zero_comp,
  end),
  refine ⟨u, v, hu.symm, hv.symm, _⟩,
  apply exact_of_pseudo_exact,
  split,
  { intro h,
    apply pseudo_injective_of_mono (kernel.ι γ),
    rw ←comp_apply,
    rw hv,
    rw ←comp_apply,
    rw ←category.assoc,
    rw hu,
    rw category.assoc,
    rw fg.1,
    rw apply_zero,
    rw has_zero_morphisms.comp_zero,
    rw zero_apply, },
  { intros b hb,
    have : g (pseudo_apply (kernel.ι β) b) = 0,
    { erw ←comp_apply,
      rw ←hv,
      rw comp_apply,
      rw hb,
      rw apply_zero, },
    cases (pseudo_exact_of_exact fg).2 (pseudo_apply (kernel.ι β) b) this with a ha,
    have : α a = 0,
    { apply pseudo_injective_of_mono f',
      rw ←comp_apply,
      rw comm₁,
      rw comp_apply,
      rw ha,
      erw ←comp_apply,
      rw kernel.condition,
      rw zero_apply,
      rw apply_zero, },
    cases (pseudo_exact_of_exact (kernel_exact α)).2 a this with a' ha',
    use a',
    apply pseudo_injective_of_mono (kernel.ι β),
    rw ←comp_apply,
    rw hu,
    rw comp_apply,
    rw ha',
    exact ha, },
end

end kernels

section cokernels
variables {P Q R P' Q' R' : V}
variables {f : P ⟶ Q} {g : Q ⟶ R} {f' : P' ⟶ Q'} {g' : Q' ⟶ R'}
variables {α : P ⟶ P'} {β : Q ⟶ Q'} {γ : R ⟶ R'}
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ)
variables (fg : exact f g) (fg' : exact f' g')
variables [epi g]

include comm₁ comm₂ fg fg'

lemma cokernels : ∃ (u : cokernel α ⟶ cokernel β) (v : cokernel β ⟶ cokernel γ),
  (cokernel.π α ≫ u = f' ≫ cokernel.π β) ∧ (cokernel.π β ≫ v = g' ≫ cokernel.π γ)
  ∧ exact u v :=
begin
  obtain ⟨u, hu⟩ := cokernel.desc' α (f' ≫ cokernel.π β) (begin
    rw ←category.assoc,
    rw comm₁,
    rw category.assoc,
    rw cokernel.condition,
    rw has_zero_morphisms.comp_zero,
  end),
  obtain ⟨v, hv⟩ := cokernel.desc' β (g' ≫ cokernel.π γ) (begin
    rw ←category.assoc,
    rw comm₂,
    rw category.assoc,
    rw cokernel.condition,
    rw has_zero_morphisms.comp_zero,
  end),
  refine ⟨u, v, hu, hv, _⟩,
  apply exact_of_pseudo_exact,
  split,
  { intro a'',
    cases pseudo_surjective_of_epi (cokernel.π α) a'' with a' ha',
    rw ←ha',
    rw ←comp_apply,
    rw ←comp_apply,
    rw ←category.assoc,
    rw hu,
    rw category.assoc,
    rw hv,
    rw ←category.assoc,
    rw fg'.1,
    rw comp_apply,
    rw zero_apply,
    rw apply_zero, },
  { intros b'' hb'',
    cases pseudo_surjective_of_epi (cokernel.π β) b'' with b' hb',
    have : (cokernel.π γ : R' ⟶ cokernel γ) (g' b') = 0,
    { rw ←comp_apply,
      rw ←hv,
      rw comp_apply,
      rw hb',
      rw hb'', },
    cases (pseudo_exact_of_exact (cokernel_exact _)).2 _ this with c hc,
    cases pseudo_surjective_of_epi g c with b hb,
    have : g' b' = g' (β b),
    { rw ←comp_apply,
      rw comm₂,
      rw ←hc,
      rw comp_apply,
      rw hb, },
    obtain ⟨bb, hbb, hbb'⟩ := sub_of_eq_image _ _ _ this,
    cases (pseudo_exact_of_exact fg').2 _ hbb with a' ha',
    use (cokernel.π α : P' ⟶ cokernel α) a',
    rw ←comp_apply,
    rw hu,
    rw comp_apply,
    rw ha',
    have := hbb' _ (cokernel.π β),
    rw ←hb',
    apply this,
    rw ←comp_apply,
    rw cokernel.condition,
    rw zero_apply, },
end

end cokernels

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
limit_kernel_fork.lift' _ (kernel_of_mono_exact _ _ δl) (γ ≫ ζ) $
  by { rw category.assoc, ext, simp only [comp_apply], commutativity }

def fill_right [mono ε] : { x : B ⟶ C // x ≫ ε = δ ≫ η } :=
limit_kernel_fork.lift' _ (kernel_of_mono_exact _ _ εμ) (δ ≫ η) $
  by { rw category.assoc, ext, simp only [comp_apply], commutativity }

variables {α : A ⟶ B} {β : B ⟶ C}
variables (comm₃ : α ≫ δ = γ ≫ ζ) (comm₄ : β ≫ ε = δ ≫ η)
include comm₃ comm₄

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

end kernels_full
