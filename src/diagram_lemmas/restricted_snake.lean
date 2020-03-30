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


--namespace restricted_snake_internal
open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.abelian.pseudoelements

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun

section
universes v u
parameters {V : Type u} [𝒞 : category.{v} V] [abelian.{v} V]
include 𝒞

parameters {A B C D E F G H I J K L : V}
parameters {α : A ⟶ B} {β : B ⟶ C} {γ : A ⟶ D} {δ : B ⟶ E} {ε : C ⟶ F}
parameters {ζ : D ⟶ E} {η : E ⟶ F} {θ : D ⟶ G} {κ : E ⟶ H} {μ : F ⟶ I}
parameters {ν : G ⟶ H} {ξ : H ⟶ I} {π : G ⟶ J} {ρ : H ⟶ K} {σ : I ⟶ L}
parameters {τ : J ⟶ K} {φ : K ⟶ L}
parameters (comm₁ : α ≫ δ = γ ≫ ζ) (comm₂ : β ≫ ε = δ ≫ η) (comm₃ : ζ ≫ κ = θ ≫ ν)
parameters (comm₄ : η ≫ μ = κ ≫ ξ) (comm₅ : ν ≫ ρ = π ≫ τ) (comm₆ : ξ ≫ σ = ρ ≫ φ)
parameters (αβ : exact α β) (ζη : exact ζ η) (νξ : exact ν ξ) (τφ : exact τ φ) (γθ : exact γ θ)
parameters (θπ : exact θ π) (δκ : exact δ κ) (κρ : exact κ ρ) (εμ : exact ε μ) (μσ : exact μ σ)
parameters [mono ζ] [epi ξ] [epi η] [mono ν] [mono ε] [epi π]
include comm₁ comm₂ comm₃ comm₄ comm₅ comm₆
include αβ ζη νξ τφ γθ θπ δκ κρ εμ μσ


parameters {comm₁} {comm₂} {comm₃} {comm₄} {comm₅} {comm₆}
parameters {αβ} {ζη} {νξ} {τφ} {γθ} {θπ} {δκ} {κρ} {εμ} {μσ}

def Z : V := pullback ε η
def Δ : Z ⟶ C := pullback.fst
def Γ : Z ⟶ E := pullback.snd
lemma comm₇ : Δ ≫ ε = Γ ≫ η := pullback.condition

instance epiΔ : epi Δ :=
begin
  dunfold Δ,
  apply_instance,
end

def Y : V := pushout π ν
def Ξ : J ⟶ Y := pushout.inl
def Λ : H ⟶ Y := pushout.inr
lemma comm₈ : π ≫ Ξ = ν ≫ Λ := pushout.condition

instance monoΞ : mono Ξ :=
begin
  dunfold Ξ,
  sorry,
end

def X := kernel Δ
def S : X ⟶ Z := kernel.ι Δ

def W := cokernel Ξ
def Υ := cokernel.π Ξ

lemma SΔ : exact S Δ := kernel_exact _
lemma ΞΥ : exact Ξ Υ := cokernel_exact _

lemma SΓη : (S ≫ Γ) ≫ η = 0 :=
begin
  rw category.assoc,
  ext,
  simp only [comp_apply],
  have := SΔ,
  have : Δ ≫ ε = Γ ≫ η := comm₇,
  commutativity,
end

def HΨ := limit_kernel_fork.lift' _ (kernel_of_mono_exact _ _ ζη) (S ≫ Γ) SΓη
def Ψ : X ⟶ D := HΨ.1
lemma hΨ : Ψ ≫ ζ = S ≫ Γ := HΨ.2

lemma νΛΥ : ν ≫ Λ ≫ Υ = 0 :=
begin
  ext,
  simp only [comp_apply],
  have := ΞΥ,
  have := comm₈,
  commutativity,
end

def HΩ := colimit_cokernel_cofork.desc' _ (cokernel_of_epi_exact _ _ νξ) (Λ ≫ Υ) νΛΥ
def Ω : I ⟶ W := HΩ.1
lemma hΩ : ξ ≫ Ω = Λ ≫ Υ := HΩ.2

lemma SΓκΛ : S ≫ Γ ≫ κ ≫ Λ = 0 :=
begin
  ext,
  simp only [comp_apply],
  have := hΨ,
  have := comm₈,
  commutativity,
end

def Δcone : cokernel_cofork S := cokernel_cofork.of_π Δ $ kernel.condition _
def Δlim : is_colimit Δcone := epi_is_cokernel_of_kernel
  (limit.cone (parallel_pair Δ 0)) (limit.is_limit _)

def Hχ := colimit_cokernel_cofork.desc' _ Δlim _ SΓκΛ
def χ : C ⟶ Y := Hχ.1
def hχ : Δ ≫ χ = Γ ≫ κ ≫ Λ := Hχ.2

lemma Υχ : χ ≫ Υ = 0 :=
begin
  apply (preadditive.cancel_zero_iff_epi Δ).1 (by apply_instance),
  ext,
  simp only [comp_apply],
  have := hχ,
  have := hΩ,
  have := comm₇,
  commutativity,
end

def Ξcone : kernel_fork Υ := kernel_fork.of_ι Ξ $ cokernel.condition _
def Ξlim : is_limit Ξcone := mono_is_kernel_of_cokernel
  (colimit.cocone (parallel_pair Ξ 0)) (colimit.is_colimit _)

def Hω := limit_kernel_fork.lift' _ Ξlim _ Υχ
def ω : C ⟶ J := Hω.1
lemma hω : ω ≫ Ξ = χ := Hω.2

lemma ω_char (c : C) (e : E) (g : G) (h₁ : η e = ε c) (h₂ : ν g = κ e) : π g = ω c :=
begin
  obtain ⟨z, hz₁, hz₂⟩ := pseudo_pullback h₁.symm,
  change Δ z = c at hz₁,
  change Γ z = e at hz₂,
  have := hω,
  have := hχ,
  have := comm₈,
  apply pseudo_injective_of_mono Ξ,
  commutativity,
end

theorem βω : exact β ω :=
begin
  have := hω,
  have := hχ,
  have := comm₇,
  have := comm₈,
  apply exact_of_pseudo_exact,
  split,
  { intro b,
    chase b using [β] with c,
    chase b using [δ] with e,
    have h₁ : η e = ε c, by commutativity,
    chase e using [κ, ν] with h g,
    have : ν g = 0, by commutativity,
    have : g = 0, -- This should be automatic!
    { apply pseudo_injective_of_mono ν,
      commutativity, },
    have h₂ : ν g = κ e, by commutativity,
    have := ω_char _ _ _ h₁ h₂,
    commutativity, },
  { intros c hc,
    chase c using [ε, η, κ, ν] with f e h g,
    have := ω_char c e g (by commutativity) (by commutativity),
    chase g using [θ] with d,
    have : κ (ζ d) = κ e, by commutativity,
    obtain ⟨z, hz₁, hz₂⟩ := sub_of_eq_image _ _ _ this.symm,
    chase z using [δ] with b,
    have : η (ζ d) = 0, by commutativity,
    have := hz₂ _ _ this,
    use b,
    commutativity, }
end

theorem ωτ : exact ω τ :=
begin
  apply exact_of_pseudo_exact,
  split,
  { intro c,
    chase c using [ε, η, κ, ν] with f e h g,
    have := ω_char c e g (by commutativity) (by commutativity),
    commutativity, },
  { intros j hj,
    chase j using [π, ν, κ, η, ε] with g h e f c,
    have := ω_char c e g (by commutativity) (by commutativity),
    use c,
    commutativity, }
end

#print ωτ
end

--end restricted_snake_internal
