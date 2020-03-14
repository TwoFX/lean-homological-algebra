import category_theory.category
import abelian
import exact
import hom_to_mathlib
import pseudoelements

open category_theory
open category_theory.limits
open category_theory.abelian

universes v u

section
variables {C : Type u} [𝒞 : category.{v} C] [𝒜 : abelian.{v} C]
include 𝒞 𝒜

variables {P Q R S P' Q' R' S' : C}
variables {f : P ⟶ Q} {g : Q ⟶ R} {h : R ⟶ S}
variables {f' : P' ⟶ Q'} {g' : Q' ⟶ R'} {h' : R' ⟶ S'}
variables {α : P ⟶ P'} {β : Q ⟶ Q'} {γ : R ⟶ R'} {δ : S ⟶ S'}
variables (fg : exact f g) (gh : exact g h) (fg' : exact f' g') (gh' : exact g' h')
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include fg gh fg' gh' comm₁ comm₂ comm₃

local attribute [instance] hom_to_fun

lemma abelian_four' (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
mono_of_zero_of_map_zero _ $ λ c hc,
begin
  have : h c = 0,
  { apply injective_of_mono δ hδ,
    rw ←comp_apply,
    rw ←comm₃,
    rw comp_apply,
    rw hc,
    rw apply_zero,
    rw apply_zero, },
  cases (exact_char g h gh).2 _ this with b hb,
  have : g' (β b) = 0,
  { rw ←comp_apply,
    rw comm₂,
    rw comp_apply,
    rw hb,
    exact hc, },
  cases (exact_char f' g' fg').2 _ this with a' ha',
  cases (category_theory.abelian.epi_iff_surjective α).1 hα a' with a ha,
  have : f a = b,
  { apply injective_of_mono β hβ,
    rw ←comp_apply,
    rw ←comm₁,
    rw comp_apply,
    rw ha,
    exact ha', },
  rw ←hb,
  rw ←this,
  rw (exact_char f g fg).1,
end

end
