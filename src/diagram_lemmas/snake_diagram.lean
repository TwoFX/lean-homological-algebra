/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import abelian
import abelian_SEMF
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
--(αβ : exact α β)
(ζη : exact ζ η) (νξ : exact ν ξ)
--(τφ : exact τ φ)
(γθ : exact γ θ)
(θπ : exact θ π) (δκ : exact δ κ) (κρ : exact κ ρ) (εμ : exact ε μ) (μσ : exact μ σ)

attribute [chase] exact_snake_diagram.comm₁ exact_snake_diagram.comm₂ exact_snake_diagram.comm₃
attribute [chase] exact_snake_diagram.comm₄ exact_snake_diagram.comm₅ exact_snake_diagram.comm₆
--attribute [chase] exact_snake_diagram.αβ
attribute [chase] exact_snake_diagram.ζη exact_snake_diagram.νξ
--attribute [chase] exact_snake_diagram.τφ
attribute [chase] exact_snake_diagram.γθ exact_snake_diagram.θπ
attribute [chase] exact_snake_diagram.δκ exact_snake_diagram.κρ exact_snake_diagram.εμ
attribute [chase] exact_snake_diagram.μσ

variable {V}

/- We need to do this instead of `attribute [chase] snake_digram.α` because the projection
   has the wrong signature: It takes a `snake_diagram` instead of an `exact_snake_diagram`. -/
@[chase] abbreviation exact_snake_α (d : exact_snake_diagram.{v} V) := d.α
@[chase] abbreviation exact_snake_β (d : exact_snake_diagram.{v} V) := d.β
@[chase] abbreviation exact_snake_γ (d : exact_snake_diagram.{v} V) := d.γ
@[chase] abbreviation exact_snake_δ (d : exact_snake_diagram.{v} V) := d.δ
@[chase] abbreviation exact_snake_ε (d : exact_snake_diagram.{v} V) := d.ε
@[chase] abbreviation exact_snake_ζ (d : exact_snake_diagram.{v} V) := d.ζ
@[chase] abbreviation exact_snake_η (d : exact_snake_diagram.{v} V) := d.η
@[chase] abbreviation exact_snake_θ (d : exact_snake_diagram.{v} V) := d.θ
@[chase] abbreviation exact_snake_κ (d : exact_snake_diagram.{v} V) := d.κ
@[chase] abbreviation exact_snake_μ (d : exact_snake_diagram.{v} V) := d.μ
@[chase] abbreviation exact_snake_ν (d : exact_snake_diagram.{v} V) := d.ν
@[chase] abbreviation exact_snake_ξ (d : exact_snake_diagram.{v} V) := d.ξ
@[chase] abbreviation exact_snake_π (d : exact_snake_diagram.{v} V) := d.π
@[chase] abbreviation exact_snake_ρ (d : exact_snake_diagram.{v} V) := d.ρ
@[chase] abbreviation exact_snake_σ (d : exact_snake_diagram.{v} V) := d.σ
@[chase] abbreviation exact_snake_τ (d : exact_snake_diagram.{v} V) := d.τ
@[chase] abbreviation exact_snake_φ (d : exact_snake_diagram.{v} V) := d.φ

--set_option profiler true

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

def HΨ := kernel_fork.is_limit.lift' (kernel_of_mono_exact _ _ d.ζη) (S d ≫ Γ d) (SΓη d)
def Ψ : (X d) ⟶ d.D := (HΨ d).1
@[chase] lemma hΨ : Ψ d ≫ d.ζ = S d ≫ Γ d := (HΨ d).2

lemma νΛΥ : d.ν ≫ (Λ d) ≫ (Υ d) = 0 :=
begin
  ext,
  simp only [comp_apply],
  commutativity at d,
end

def HΩ := cokernel_cofork.is_colimit.desc' (cokernel_of_epi_exact _ _ d.νξ) (Λ d ≫ Υ d) (νΛΥ d)
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

def Hχ := cokernel_cofork.is_colimit.desc' (Δlim d) _ (SΓκΛ d)
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

def Hω := kernel_fork.is_limit.lift' (Ξlim d) _ (Υχ d)
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
    exact ⟨c, by commutativity⟩ }
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

namespace internal
variable (d : exact_snake_diagram.{v} V)
variables [mono d.ν] [epi d.η] [mono d.δ] [mono d.ε] [epi d.π] [epi d.ρ]

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun

abbreviation Z : V := kernel (cokernel.π d.ζ)
@[chase] abbreviation ζ₁ : d.D ⟶ (Z d) := factor_thru_image d.ζ
@[chase] abbreviation ζ₂ : (Z d) ⟶ d.E := kernel.ι (cokernel.π d.ζ)

instance strong_epi_ζ : strong_epi (ζ₁ d) :=
strong_epi_of_epi _

@[chase] abbreviation Γ : (Z d) ⟶ d.G := diag_lift $
  show d.θ ≫ (𝟙 d.G ≫ d.ν) = (ζ₁ d ≫ ζ₂ d) ≫ d.κ, from
  begin
    rw abelian.image.fac,
    rw category.id_comp,
    exact d.comm₃.symm,
  end

@[chase] lemma hΓ₁ : (ζ₁ d) ≫ (Γ d) = d.θ :=
begin
  rw diag_lift_fac_left,
  rw category.comp_id
end

@[chase] lemma hΓ₂ : (ζ₂ d) ≫ d.κ = (Γ d) ≫ d.ν :=
eq.symm $ diag_lift_fac_right _

abbreviation W : V := kernel (cokernel.π d.ξ)
abbreviation ξ₁ : d.H ⟶ (W d) := factor_thru_image d.ξ
abbreviation ξ₂ : (W d) ⟶ d.I := kernel.ι (cokernel.π d.ξ)

instance strong_epi_ξ : strong_epi (ξ₁ d) :=
strong_epi_of_epi _

instance strong_epi_η : strong_epi d.to_snake_diagram.η :=
strong_epi_of_epi _

@[chase] def Δ : d.F ⟶ (W d) :=
diag_lift $ show d.κ ≫ (ξ₁ d ≫ ξ₂ d) = (d.η ≫ 𝟙 d.F) ≫ d.μ, from
begin
  erw abelian.image.fac d.ξ,
  rw category.assoc,
  rw category.id_comp,
  exact d.comm₄.symm
end

@[chase] lemma hΔ₁ : d.η ≫ (Δ d) = d.κ ≫ (ξ₁ d) :=
diag_lift_fac_left _

@[chase] lemma hΔ₂ : d.μ = (Δ d) ≫ (ξ₂ d) :=
begin
  rw ←category.id_comp d.μ,
  exact (diag_lift_fac_right _).symm
end

abbreviation V' : V := kernel (Γ d)
abbreviation Λ : (V' d) ⟶ (Z d) := kernel.ι (Γ d)

abbreviation U : V := kernel (Δ d)
abbreviation Ξ : (U d) ⟶ d.F := kernel.ι (Δ d)

abbreviation T : V := cokernel (Γ d)
abbreviation S : d.G ⟶ (T d) := cokernel.π (Γ d)

abbreviation S' : V := cokernel (Δ d)
abbreviation Υ : (W d) ⟶ (S' d) := cokernel.π (Δ d)

set_option trace.app_builder true
--set_option pp.all true

abbreviation Hα₁ := kernel.lift' (Γ d) (d.γ ≫ (ζ₁ d)) $
  by rw [category.assoc, hΓ₁, d.γθ.1]
abbreviation α₁ : d.A ⟶ (V' d) := (Hα₁ d).1
@[chase] lemma hα₁ : α₁ d ≫ Λ d = d.γ ≫ (ζ₁ d) := (Hα₁ d).2

abbreviation Hα₂ := kernel_fork.is_limit.lift' (kernel_of_mono_exact _ _ d.δκ) (Λ d ≫ ζ₂ d) $
  by rw [category.assoc, hΓ₂, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp]
abbreviation α₂ : V' d ⟶ d.B := (Hα₂ d).1
@[chase] lemma hα₂ : α₂ d ≫ d.δ = Λ d ≫ ζ₂ d := (Hα₂ d).2

abbreviation Hβ₁ := kernel.lift' (Δ d) (d.δ ≫ d.η) $
  by rw [category.assoc, hΔ₁, ←category.assoc, d.δκ.1, has_zero_morphisms.zero_comp]
abbreviation β₁ : d.B ⟶ (U d) := (Hβ₁ d).1
@[chase] lemma hβ₁ : β₁ d ≫ Ξ d = d.δ ≫ d.η := (Hβ₁ d).2

abbreviation Hβ₂ := kernel_fork.is_limit.lift' (kernel_of_mono_exact _ _ d.εμ) (Ξ d) $
  by rw [hΔ₂, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp]
abbreviation β₂ : U d ⟶ d.C := (Hβ₂ d).1
@[chase] lemma hβ₂ : β₂ d ≫ d.ε = Ξ d := (Hβ₂ d).2

lemma β₁β₂ : β₁ d ≫ β₂ d = d.β :=
begin
  apply fork.is_limit.hom_ext (kernel_of_mono_exact _ _ d.εμ),
  erw [category.assoc, hβ₂, hβ₁, d.comm₂]
end

abbreviation Hτ₁ := cokernel_cofork.is_colimit.desc' (cokernel_of_epi_exact _ _ d.θπ) (S d) $
  by rw [←hΓ₁, category.assoc, cokernel.condition, has_zero_morphisms.comp_zero]
abbreviation τ₁ : d.J ⟶ (T d) := (Hτ₁ d).1
@[chase] lemma hτ₁ : d.π ≫ (τ₁ d) = S d := (Hτ₁ d).2

abbreviation Hτ₂ := cokernel.desc' (Γ d) (d.ν ≫ d.ρ) $
  by rw [←category.assoc, ←hΓ₂, category.assoc, d.κρ.1, has_zero_morphisms.comp_zero]
abbreviation τ₂ : T d ⟶ d.K := (Hτ₂ d).1
@[chase] lemma hτ₂ : S d ≫ τ₂ d = d.ν ≫ d.ρ := (Hτ₂ d).2

lemma τ₁τ₂ : τ₁ d ≫ τ₂ d = d.τ :=
begin
  apply cofork.is_colimit.hom_ext (cokernel_of_epi_exact _ _ d.θπ),
  erw [←category.assoc, hτ₁, hτ₂, ←d.comm₅]
end

abbreviation Hφ₁ := cokernel_cofork.is_colimit.desc' (cokernel_of_epi_exact _ _ d.κρ) (ξ₁ d ≫ Υ d) $
  by rw [←category.assoc, ←hΔ₁, category.assoc, cokernel.condition, has_zero_morphisms.comp_zero]
abbreviation φ₁ : d.K ⟶ S' d := (Hφ₁ d).1
@[chase] lemma hφ₁ : d.ρ ≫ φ₁ d = ξ₁ d ≫ Υ d := (Hφ₁ d).2

@[chase] lemma ΞΔ : exact (Ξ d) (Δ d) := kernel_exact _
@[chase] lemma ΓS : exact (Γ d) (S d) := cokernel_exact _

instance β₂_mono : mono (β₂ d) :=
mono_of_mono_fac $ hβ₂ d

instance β₂_epi : epi (β₂ d) :=
begin
  apply epi_of_pseudo_surjective,
  intro c,
  chase c using [d.ε] with f,
  have : (Δ d : _ ⟶ _) f = 0,
  { apply pseudo_injective_of_mono (ξ₂ d),
    rw ←comp_apply,
    rw ←hΔ₂,
    rw ←h.f,
    rw ←comp_apply,
    rw d.εμ.1,
    rw zero_apply,
    rw apply_zero, },
  chase f using [Ξ d] with u at d,
  use u,
  apply pseudo_injective_of_mono d.ε,
  commutativity at d,
end

instance β₂_iso : is_iso (β₂ d) :=
mono_epi_iso _

instance τ₁_epi : epi (τ₁ d) :=
epi_of_epi_fac $ hτ₁ d

instance τ₁_mono : mono (τ₁ d) :=
begin
  apply mono_of_zero_of_map_zero,
  intros j hj,
  chase j using [d.π] with g at d,
  have : (S d : _ ⟶ _) g = 0,
  { rw [←hτ₁, comp_apply, h.g, hj], },
  chase g using [Γ d] with z at d,
  obtain ⟨e, he⟩ := pseudo_surjective_of_epi (ζ₁ d) z,
  rw [←h.g, ←h.z, ←he, ←comp_apply, ←comp_apply, ←category.assoc, hΓ₁, d.θπ.1, zero_apply],
end

instance τ₁_iso : is_iso (τ₁ d) :=
mono_epi_iso _

abbreviation inner_diagram : exact_snake_diagram.{v} V :=
{ A := V' d, B := d.B, C := U d, D := Z d, E := d.E, F := d.F,
  G := d.G, H := d.H, I := W d, J := T d, K := d.K, L := S' d,
  α := α₂ d,
  β := β₁ d,
  γ := Λ d,
  δ := d.δ,
  ε := Ξ d,
  ζ := ζ₂ d,
  η := d.η,
  θ := Γ d,
  κ := d.κ,
  μ := Δ d,
  ν := d.ν,
  ξ := ξ₁ d,
  π := S d,
  ρ := d.ρ,
  σ := Υ d,
  τ := τ₂ d,
  φ := φ₁ d,
  comm₁ := hα₂ d,
  comm₂ := hβ₁ d,
  comm₃ := hΓ₂ d,
  comm₄ := hΔ₁ d,
  comm₅ := (hτ₂ d).symm,
  comm₆ := (hφ₁ d).symm,
  ζη := image_exact _ _ d.ζη,
  νξ := exact_image _ _ d.νξ,
  γθ := kernel_exact _,
  θπ := cokernel_exact _,
  δκ := d.δκ,
  κρ := d.κρ,
  εμ := kernel_exact _,
  μσ := cokernel_exact _ }

abbreviation ω' : U d ⟶ T d := restricted.connecting_morphism (inner_diagram d)

abbreviation ω : d.C ⟶ d.J := inv (β₂ d) ≫ ω' d ≫ inv (τ₁ d)

lemma βω : exact d.β (ω d) :=
begin
  have : exact (β₁ d) (ω' d) := restricted.exact₁ (inner_diagram d),
  have := exact_iso_right _ _ (as_iso (inv (τ₁ d))) this,
  have : exact (β₁ d ≫ β₂ d) (ω d) := exact_iso _ _ (as_iso (β₂ d)) this,
  rw β₁β₂ at this,
  exact this,
end

lemma ωτ : exact (ω d) (d.τ) :=
begin
  have := restricted.exact₂ (inner_diagram d),
  have := exact_iso _ _ (as_iso (inv (τ₁ d))) this,
  have : exact (ω d) (τ₁ d ≫ τ₂ d) := exact_iso_left _ _ (as_iso (inv (β₂ d))) this,
  rw τ₁τ₂ at this,
  exact this,
end

end internal

variable (d : exact_snake_diagram.{v} V)
variables [mono d.ν] [epi d.η] [mono d.δ] [mono d.ε] [epi d.π] [epi d.ρ]

def connecting_morphism : d.C ⟶ d.J :=
internal.ω d

theorem exact₁ : exact d.β (connecting_morphism d) :=
internal.βω d

theorem exact₂ : exact (connecting_morphism d) d.τ :=
internal.ωτ d

end category_theory.abelian.diagram_lemmas.snake
