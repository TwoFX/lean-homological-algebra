import category_theory.category
import abelian
import exact
import hom_to_mathlib
import pseudoelements

open category_theory
open category_theory.limits
open category_theory.abelian

local attribute [instance] hom_to_fun

universes v u
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

section four
variables {P Q R S P' Q' R' S' : C}
variables {f : P ⟶ Q} {g : Q ⟶ R} {h : R ⟶ S}
variables {f' : P' ⟶ Q'} {g' : Q' ⟶ R'} {h' : R' ⟶ S'}
variables {α : P ⟶ P'} {β : Q ⟶ Q'} {γ : R ⟶ R'} {δ : S ⟶ S'}
variables (fg : exact f g) (gh : exact g h) (fg' : exact f' g') (gh' : exact g' h')
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include fg gh fg' gh' comm₁ comm₂ comm₃

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

end four

section kernels
variables {P Q R P' Q' R' : C}
variables {f : P ⟶ Q} {g : Q ⟶ R} {f' : P' ⟶ Q'} {g' : Q' ⟶ R'}
variables {α : P ⟶ P'} {β : Q ⟶ Q'} {γ : R ⟶ R'}
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ)
variables (fg : exact f g) (fg' : exact f' g')
variables [mono f']

include comm₁ comm₂ fg fg'

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
  apply exact_char',
  split,
  { intro h,
    apply injective_of_mono (kernel.ι γ) (by apply_instance),
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
    cases (exact_char f g fg).2 (pseudo_apply (kernel.ι β) b) this with a ha,
    have : α a = 0,
    { apply injective_of_mono f' (by apply_instance),
      rw ←comp_apply,
      rw comm₁,
      rw comp_apply,
      rw ha,
      erw ←comp_apply,
      rw kernel.condition,
      rw zero_apply,
      rw apply_zero, },
    cases (exact_char (kernel.ι α) α (kernel_exact α)).2 a this with a' ha',
    use a',
    apply injective_of_mono (kernel.ι β) (by apply_instance),
    rw ←comp_apply,
    rw hu,
    rw comp_apply,
    rw ha',
    exact ha, },
end

end kernels

section cokernels
variables {P Q R P' Q' R' : C}
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
  apply exact_char',
  split,
  { intro a'',
    cases (category_theory.abelian.epi_iff_surjective (cokernel.π α)).1 (by apply_instance) a'' with a' ha',
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
    cases (category_theory.abelian.epi_iff_surjective (cokernel.π β)).1 (by apply_instance) b'' with b' hb',
    have : (cokernel.π γ : R' ⟶ cokernel γ) (g' b') = 0,
    { rw ←comp_apply,
      rw ←hv,
      rw comp_apply,
      rw hb',
      rw hb'', },
    cases (exact_char γ (cokernel.π γ) (cokernel_exact _)).2 _ this with c hc,
    cases (category_theory.abelian.epi_iff_surjective g).1 (by apply_instance) c with b hb,
    have : g' b' = g' (β b),
    { rw ←comp_apply,
      rw comm₂,
      rw ←hc,
      rw comp_apply,
      rw hb, },
    obtain ⟨bb, hbb, hbb'⟩ := sub _ _ _ this,
    cases (exact_char f' g' fg').2 _ hbb with a' ha',
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