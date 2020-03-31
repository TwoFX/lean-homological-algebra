/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import abelian
import exact
import tactic.diagram_chase

open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.abelian.pseudoelements

namespace category_theory.abelian.diagram_lemmas.snake

universes v u
variables (V : Type u) [𝒞 : category.{v} V] [abelian.{v} V]
include 𝒞

structure snake_diagram :=
(A B C D E F G H I J K L : V)
(α : A ⟶ B) (β : B ⟶ C) (γ : A ⟶ D) (δ : B ⟶ E) (ε : C ⟶ F)
(ζ : D ⟶ E) (η : E ⟶ F) (θ : D ⟶ G) (κ : E ⟶ H) (μ : F ⟶ I)
(ν : G ⟶ H) (ξ : H ⟶ I) (π : G ⟶ J) (ρ : H ⟶ K) (σ : I ⟶ L)
(τ : J ⟶ K) (φ : K ⟶ L)

structure exact_snake_diagram extends snake_diagram.{v} V :=
(comm₁ : α ≫ δ = γ ≫ ζ) (comm₂ : β ≫ ε = δ ≫ η) (comm₃ : ζ ≫ κ = θ ≫ ν)
(comm₄ : η ≫ μ = κ ≫ ξ) (comm₅ : ν ≫ ρ = π ≫ τ) (comm₆ : ξ ≫ σ = ρ ≫ φ)
(αβ : exact α β) (ζη : exact ζ η) (νξ : exact ν ξ) (τφ : exact τ φ) (γθ : exact γ θ)
(θπ : exact θ π) (δκ : exact δ κ) (κρ : exact κ ρ) (εμ : exact ε μ) (μσ : exact μ σ)

attribute [chase] exact_snake_diagram.comm₁ exact_snake_diagram.comm₂ exact_snake_diagram.comm₃
attribute [chase] exact_snake_diagram.comm₄ exact_snake_diagram.comm₅ exact_snake_diagram.comm₆
attribute [chase] exact_snake_diagram.αβ exact_snake_diagram.ζη exact_snake_diagram.νξ
attribute [chase] exact_snake_diagram.τφ exact_snake_diagram.γθ exact_snake_diagram.θπ
attribute [chase] exact_snake_diagram.δκ exact_snake_diagram.κρ exact_snake_diagram.εμ
attribute [chase] exact_snake_diagram.μσ

variable {V}

@[chase] abbreviation myα (d : exact_snake_diagram.{v} V) := d.α
@[chase] abbreviation myβ (d : exact_snake_diagram.{v} V) := d.β
@[chase] abbreviation myγ (d : exact_snake_diagram.{v} V) := d.γ
@[chase] abbreviation myδ (d : exact_snake_diagram.{v} V) := d.δ
@[chase] abbreviation myε (d : exact_snake_diagram.{v} V) := d.ε
@[chase] abbreviation myζ (d : exact_snake_diagram.{v} V) := d.ζ
@[chase] abbreviation myη (d : exact_snake_diagram.{v} V) := d.η
@[chase] abbreviation myθ (d : exact_snake_diagram.{v} V) := d.θ
@[chase] abbreviation myκ (d : exact_snake_diagram.{v} V) := d.κ
@[chase] abbreviation myμ (d : exact_snake_diagram.{v} V) := d.μ
@[chase] abbreviation myν (d : exact_snake_diagram.{v} V) := d.ν
@[chase] abbreviation myξ (d : exact_snake_diagram.{v} V) := d.ξ
@[chase] abbreviation myπ (d : exact_snake_diagram.{v} V) := d.π
@[chase] abbreviation myρ (d : exact_snake_diagram.{v} V) := d.ρ
@[chase] abbreviation myσ (d : exact_snake_diagram.{v} V) := d.σ
@[chase] abbreviation myτ (d : exact_snake_diagram.{v} V) := d.τ
@[chase] abbreviation myφ (d : exact_snake_diagram.{v} V) := d.φ

namespace restricted

namespace internal
variable (d : exact_snake_diagram.{v} V)
variables [mono d.ζ] [epi d.ξ] [epi d.η] [mono d.ν] [mono d.ε] [epi d.π]

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun

abbreviation Z : V := pullback d.ε d.η
abbreviation Δ : (Z d) ⟶ d.C := pullback.fst
abbreviation Γ : (Z d) ⟶ d.E := pullback.snd
@[chase] lemma comm₇ : (Δ d) ≫ d.ε = (Γ d) ≫ d.η := pullback.condition

abbreviation Y : V := pushout d.π d.ν
abbreviation Ξ : d.J ⟶ (Y d) := pushout.inl
abbreviation Λ : d.H ⟶ (Y d) := pushout.inr
@[chase] lemma comm₈ : d.π ≫ (Ξ d) = d.ν ≫ (Λ d) := pushout.condition

abbreviation X : V := kernel (Δ d)
abbreviation S : (X d) ⟶ (Z d) := kernel.ι (Δ d)

def W := cokernel (Ξ d)
def Υ := cokernel.π (Ξ d)

@[chase] lemma SΔ : exact (S d) (Δ d) := kernel_exact _
@[chase] lemma ΞΥ : exact (Ξ d) (Υ d) := cokernel_exact _

lemma SΓη : (S d ≫ Γ d) ≫ d.η = 0 :=
begin
  rw category.assoc,
  ext,
  simp only [comp_apply],
  commutativity at d,
end

def HΨ := limit_kernel_fork.lift' _ (kernel_of_mono_exact _ _ d.ζη) (S d ≫ Γ d) (SΓη d)
def Ψ : (X d) ⟶ d.D := (HΨ d).1
@[chase] lemma hΨ : Ψ d ≫ d.ζ = S d ≫ Γ d := (HΨ d).2

lemma νΛΥ : d.ν ≫ (Λ d) ≫ (Υ d) = 0 :=
begin
  ext,
  simp only [comp_apply],
  commutativity at d,
end

def HΩ := colimit_cokernel_cofork.desc' _ (cokernel_of_epi_exact _ _ d.νξ) (Λ d ≫ Υ d) (νΛΥ d)
def Ω : d.I ⟶ (W d) := (HΩ d).1
@[chase] lemma hΩ : d.ξ ≫ (Ω d) = (Λ d) ≫ (Υ d) := (HΩ d).2

lemma SΓκΛ : S d ≫ Γ d ≫ d.κ ≫ Λ d = 0 :=
begin
  ext,
  simp only [comp_apply],
  commutativity at d,
end

def Δcone : cokernel_cofork (S d) := cokernel_cofork.of_π (Δ d) $ kernel.condition _
def Δlim : is_colimit (Δcone d) := epi_is_cokernel_of_kernel
  (limit.cone (parallel_pair (Δ d) 0)) (limit.is_limit _)

def Hχ := colimit_cokernel_cofork.desc' _ (Δlim d) _ (SΓκΛ d)
def χ : d.C ⟶ (Y d) := (Hχ d).1
@[chase] lemma hχ : (Δ d) ≫ (χ d) = (Γ d) ≫ d.κ ≫ (Λ d) := (Hχ d).2

lemma Υχ : (χ d) ≫ (Υ d) = 0 :=
begin
  apply (preadditive.cancel_zero_iff_epi (Δ d)).1 (by apply_instance),
  ext,
  simp only [comp_apply],
  commutativity at d,
end

def Ξcone : kernel_fork (Υ d) := kernel_fork.of_ι (Ξ d) $ cokernel.condition _
def Ξlim : is_limit (Ξcone d) := mono_is_kernel_of_cokernel
  (colimit.cocone (parallel_pair (Ξ d) 0)) (colimit.is_colimit _)

def Hω := limit_kernel_fork.lift' _ (Ξlim d) _ (Υχ d)
def ω : d.C ⟶ d.J := (Hω d).1
@[chase] lemma hω : (ω d) ≫ (Ξ d) = (χ d) := (Hω d).2

lemma ω_char (c : d.C) (e : d.E) (g : d.G) (h₁ : d.η e = d.ε c) (h₂ : d.ν g = d.κ e) :
  d.π g = (ω d) c :=
begin
  obtain ⟨z, hz₁, hz₂⟩ := pseudo_pullback h₁.symm,
  change (Δ d : Z d ⟶ d.C) z = c at hz₁,
  change (Γ d : Z d → d.E) z = e at hz₂,
  apply pseudo_injective_of_mono (Ξ d),
  commutativity at d,
end

theorem βω : exact d.β (ω d) :=
begin
  apply exact_of_pseudo_exact,
  split,
  { intro b,
    chase b using [d.β] with c,
    chase b using [d.δ] with e,
    have h₁ : d.η e = d.ε c, by commutativity at d,
    chase e using [d.κ, d.ν] with h g at d,
    have : d.ν g = 0, by commutativity at d,
    have : g = 0, -- This should be automatic!
    { apply pseudo_injective_of_mono d.ν,
      commutativity at d, },
    have h₂ : d.ν g = d.κ e, by commutativity,
    have := ω_char d _ _ _ h₁ h₂,
    commutativity, },
  { intros c hc,
    chase c using [d.ε, d.η, d.κ, d.ν] with f e h g at d,
    have := ω_char _ c e g (by commutativity) (by commutativity),
    chase g using [d.θ] with d' at d,
    have : d.κ (d.ζ d') = d.κ e, by commutativity at d,
    obtain ⟨z, hz₁, hz₂⟩ := sub_of_eq_image _ _ _ this.symm,
    chase z using [d.δ] with b at d,
    have : d.η (d.ζ d') = 0, by commutativity at d,
    have := hz₂ _ _ this,
    use b,
    apply pseudo_injective_of_mono d.ε, -- This should also be automatic
    commutativity at d, }
end

theorem ωτ : exact (ω d) d.τ :=
begin
  apply exact_of_pseudo_exact,
  split,
  { intro c,
    chase c using [d.ε, d.η, d.κ, d.ν] with f e h g at d,
    have := ω_char _ c e g (by commutativity) (by commutativity),
    commutativity at d, },
  { intros j hj,
    chase j using [d.π, d.ν, d.κ, d.η, d.ε] with g h e f c at d,
    have := ω_char _ c e g (by commutativity) (by commutativity),
    use c,
    commutativity, }
end

end internal

variable (d : exact_snake_diagram.{v} V)
variables [mono d.ζ] [epi d.ξ] [epi d.η] [mono d.ν] [mono d.ε] [epi d.π]

def connecting_morphism : d.C ⟶ d.J :=
internal.ω d

theorem exact₁ : exact d.β (connecting_morphism d) :=
internal.βω d

theorem exact₂ : exact (connecting_morphism d) d.τ :=
internal.ωτ d

end restricted


end category_theory.abelian.diagram_lemmas.snake
