import category_theory.category
import abelian

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian


section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- mathlib #2100
instance epi_comp {X Y Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [epi g] : epi (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_epi g).1,
  apply (cancel_epi f).1,
  simpa using w,
end
instance mono_comp {X Y Z : C} (f : X ⟶ Y) [mono f] (g : Y ⟶ Z) [mono g] : mono (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_mono f).1,
  apply (cancel_mono g).1,
  simpa using w,
end

end


section
variables {C : Type u} [𝒞 : category.{v} C] [𝒜 : abelian.{v} C]
include 𝒞 𝒜

def with_codomain (P : C) := Σ Q, Q ⟶ P

def coe_with_codomain {P Q : C} : has_coe (Q ⟶ P) (with_codomain P) :=
{ coe := λ f, ⟨Q, f⟩ }

local attribute [instance] coe_with_codomain

def pseudo_equal (P : C) (f g : with_codomain P) : Prop :=
∃ (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) [epi p] [epi q], p ≫ f.2 = q ≫ g.2

lemma pseudo_equal_refl {P : C} : reflexive (pseudo_equal P) :=
λ f, ⟨f.1, 𝟙 f.1, 𝟙 f.1, by apply_instance, by apply_instance, by simp⟩

lemma pseudo_equal_symm {P : C} : symmetric (pseudo_equal P) :=
λ f g ⟨R, p, q, ep, eq, comm⟩, ⟨R, q, p, eq, ep, comm.symm⟩

lemma pseudo_equal_trans {P : C} : transitive (pseudo_equal P) :=
λ f g h ⟨R, p, q, ep, eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩,
begin
  use pullback q p',
  use pullback.fst ≫ p,
  use pullback.snd ≫ q',
  split,
  resetI,
  apply_instance,
  split,
  resetI,
  apply_instance,
  rw category.assoc,
  rw comm,
  rw ←category.assoc,
  rw pullback.condition,
  rw category.assoc,
  rw comm',
  rw category.assoc,
end

lemma pseudo_equal_equiv {P : C} : equivalence (pseudo_equal P) :=
⟨pseudo_equal_refl, pseudo_equal_symm, pseudo_equal_trans⟩

def pseudoelements.setoid (P : C) : setoid (with_codomain P) :=
{ r := pseudo_equal P,
  iseqv := pseudo_equal_equiv }

local attribute [instance] pseudoelements.setoid

def pseudoelements (P : C) := quotient (pseudoelements.setoid P)

def mk_pseudo (P : C) : with_codomain P → pseudoelements P := quot.mk (pseudo_equal P)

def coe_to_pseudo {P : C} : has_coe (with_codomain P) (pseudoelements P) := ⟨mk_pseudo P⟩

local attribute [instance] coe_to_pseudo

def app {P Q : C} (f : P ⟶ Q) (a : with_codomain P) : with_codomain Q :=
⟨a.1, a.2 ≫ f⟩

lemma pseudo_apply_aux {P Q : C} (f : P ⟶ Q) (a b : with_codomain P) :
  a ≈ b → ⟦app f a⟧ = ⟦app f b⟧ :=
λ ⟨R, p, q, ep, eq, comm⟩, quotient.sound ⟨R, p, q, ep, eq, begin
    change p ≫ (a.2 ≫ f) = q ≫ (b.2 ≫ f),
    rw ←category.assoc,
    rw comm,
    rw category.assoc,
  end⟩

def pseudo_apply {P Q : C} (f : P ⟶ Q) : pseudoelements P → pseudoelements Q :=
quotient.lift (λ (g : with_codomain P), ⟦app f g⟧) (pseudo_apply_aux f)

def hom_to_fun {P Q : C} : has_coe_to_fun (P ⟶ Q) := ⟨_, pseudo_apply⟩


local attribute [instance] hom_to_fun

lemma pseudo_apply_calc {P Q : C} (f : P ⟶ Q) (a : with_codomain P) : f ⟦a⟧ = ⟦a.2 ≫ f⟧ :=
rfl

lemma comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : pseudoelements P) :
  (f ≫ g) a = g (f a) :=
quotient.induction_on a $ λ x, quotient.sound $ by unfold app; rw category.assoc

lemma pseudo_zero_aux {P : C} (Q : C) (f : with_codomain P) : f ≈ (0 : Q ⟶ P) ↔ f.2 = 0 :=
begin
  split,
  { rintro ⟨R, p, q, ep, eq, comm⟩,
    apply (@additive.cancel_zero_iff_epi _ _ _ _ _ p).1 ep _ f.snd,
    rw comm,
    erw has_zero_morphisms.comp_zero, },
  { intro hf,
    use biproduct f.1 Q,
    use biproduct.π₁,
    use biproduct.π₂,
    split,
    apply_instance,
    split,
    apply_instance,
    rw hf,
    rw has_zero_morphisms.comp_zero,
    erw has_zero_morphisms.comp_zero, }
end

def pseudo_zero {P : C} : pseudoelements P := ⟦(0 : P ⟶ P)⟧

instance {P : C} : has_zero (pseudoelements P) := ⟨pseudo_zero⟩

lemma pseudo_zero_iff {P : C} (a : with_codomain P) : (a : pseudoelements P) = 0 ↔ a.2 = 0 :=
by rw ←pseudo_zero_aux P a; exact quotient.eq

lemma apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0 :=
begin
  erw pseudo_apply_calc,
  erw has_zero_morphisms.zero_comp,
  apply quotient.sound,
  apply (pseudo_zero_aux _ _).2,
  refl,
end

lemma zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ ∀ (a : pseudoelements P), f a = 0 :=
begin
  split,
  { intros h abar,
    apply quotient.induction_on abar,
    intro a,
    apply quotient.sound,
    apply (pseudo_zero_aux _ _).2,
    change a.2 ≫ f = 0,
    rw h,
    rw has_zero_morphisms.comp_zero, },
  { intro h,
    rw ←category.id_comp _ f,
    apply (pseudo_zero_iff ((𝟙 P ≫ f) : with_codomain Q)).1,
    exact h (𝟙 P), }
end

/-- TODO: Rewrite as tfae with f(x) = 0 → x = 0 -/
lemma mono_iff_injective {P Q : C} (f : P ⟶ Q) : mono f ↔ function.injective f :=
begin
  split,
  { intros m abar abar',
    apply quotient.induction_on₂ abar abar',
    intros a a' ha,
    rw pseudo_apply_calc at ha,
    rw pseudo_apply_calc at ha,
    obtain ⟨R, p, q, ep, eq, comm⟩ := quotient.exact ha,
    change p ≫ (a.2 ≫ f) = q ≫ (a'.2 ≫ f) at comm,
    apply quotient.sound,
    rw ←category.assoc at comm,
    rw ←category.assoc at comm,
    resetI,
    have comm' := (cancel_mono f).1 comm,
    exact ⟨R, p, q, ep, eq, comm'⟩, },
  { intro h,
    apply additive.cancel_zero_iff_mono.2,
    intros R g hg,
    have hg' : f g = 0 := (pseudo_zero_iff ⟨R, g ≫ f⟩).2 hg,
    rw ←apply_zero f at hg',
    have hx := h hg',
    apply (pseudo_zero_iff (g : with_codomain P)).1,
    exact hx, }
end

set_option trace.app_builder true

lemma epi_iff_surjective {P Q : C} (f : P ⟶ Q) : epi f ↔ function.surjective f :=
begin
  split,
  { intros h qbar,
    apply quotient.induction_on qbar,
    intro q,
    let a : pullback f q.2 ⟶ P := pullback.fst,
    use a,
    erw pseudo_apply_calc,
    apply quotient.sound,
    conv_lhs { change (a ≫ f : with_codomain Q), },
    resetI,
    refine ⟨pullback f q.2, 𝟙 (pullback f q.2), pullback.snd, by apply_instance, by apply_instance, _⟩,
    rw category.id_comp,
    erw pullback.condition,
    refl, },
  { intro h,
    have ha := h (𝟙 Q),
    cases ha with pbar hp,
    obtain ⟨p, hpp⟩ := quotient.exists_rep pbar,
    rw ←hpp at hp,
    erw pseudo_apply_calc at hp,
    obtain ⟨R, x, y, ex, ey, comm⟩ := quotient.exact hp,
    change x ≫ p.2 ≫ f = y ≫ 𝟙 Q at comm,
    rw ←category.assoc at comm,
    erw category.comp_id at comm,
    apply @epi_of_comp_epi _ _ _ _ _ (x ≫ p.snd) f,
    rw comm,
    exact ey, }
end

end

end category_theory.abelian