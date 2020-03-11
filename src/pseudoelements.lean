import category_theory.category
import abelian
import exact
import to_mathlib

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

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

lemma zero_eq_zero {P Q R : C} : ⟦((0 : Q ⟶ P) : with_codomain P)⟧ = ⟦((0 : R ⟶ P) : with_codomain P)⟧ :=
begin
  apply quotient.sound,
  apply (pseudo_zero_aux R _).2,
  refl,
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

lemma zero_apply {P Q : C} (a : pseudoelements P) : (0 : P ⟶ Q) a = 0 :=
begin
  apply quotient.induction_on a,
  intro a',
  erw pseudo_apply_calc,
  erw has_zero_morphisms.comp_zero,
  exact zero_eq_zero,
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

lemma injective_of_mono {P Q : C} (f : P ⟶ Q) : mono f → function.injective f :=
begin
  intros m abar abar',
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
  exact ⟨R, p, q, ep, eq, comm'⟩,
end

lemma zero_of_map_zero {P Q : C} (f : P ⟶ Q) : function.injective f → ∀ a, f a = 0 → a = 0 :=
begin
  intros h a ha,
  rw ←apply_zero f at ha,
  exact h ha,
end

lemma mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0 → a = 0) → mono f :=
begin
  intro h,
  apply additive.cancel_zero_iff_mono.2,
  intros R g hg,
  have hg' : f g = 0 := (pseudo_zero_iff ⟨R, g ≫ f⟩).2 hg,
  have hx := h _ hg',
  apply (pseudo_zero_iff (g : with_codomain P)).1,
  exact hx,
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

lemma exact_char {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
  exact f g → (∀ a, g (f a) = 0) ∧ (∀ b, g b = 0 → ∃ a, f a = b) :=
begin
  intro h,
  split,
  { intro a,
    rw ←comp_apply,
    rw h.1,
    exact zero_apply _, },
  { intro b',
    apply quotient.induction_on b',
    intros b hb,
    set i := kernel.ι (cokernel.π f),
    let p := to_im f,
    have hb' : b.2 ≫ g = 0,
    { rw pseudo_apply_calc at hb,
      have hb'' := (pseudo_zero_iff _).1 hb,
      exact hb'', },
    let b_cone : fork g 0 := fork.of_ι b.2 (begin
      rw hb', rw has_zero_morphisms.comp_zero,
    end),
    let c : b.1 ⟶ kernel (cokernel.π f) := is_limit.lift (exact_ker _ _ h) b_cone,
    let Y := pullback p c,
    let a : Y ⟶ P := pullback.fst,
    use a,
    erw pseudo_apply_calc,
    change ⟦(a ≫ f : with_codomain Q)⟧ = ⟦b⟧,
    apply quotient.sound,
    refine ⟨Y, 𝟙 Y, pullback.snd, by apply_instance, by apply_instance, _⟩,
    change 𝟙 Y ≫ a ≫ f = pullback.snd ≫ b.2,
    rw category.id_comp,
    conv_lhs { congr, skip, rw ←f_factor f, },
    rw ←category.assoc,
    rw pullback.condition,
    rw category.assoc,
    congr,
    exact is_limit.fac (exact_ker _ _ h) b_cone walking_parallel_pair.zero, }
end

lemma comp_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 → f a = 0 :=
begin
  intro h,
  erw pseudo_apply_calc,
  erw h,
  exact zero_eq_zero,
end

lemma exact_char' {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
  (∀ a, g (f a) = 0) ∧ (∀ b, g b = 0 → ∃ a, f a = b) → exact f g :=
begin
  rintro ⟨h₁, h₂⟩,
  have : f ≫ g = 0,
  { apply (zero_iff _).2,
    intro a,
    rw comp_apply,
    exact h₁ a, },
  fsplit,
  exact this,
  { set i := kernel.ι (cokernel.π f),
    let p := to_im f,
    have gip : p ≫ i ≫ g = 0,
    { rw ←category.assoc, rw f_factor, exact this },
    have gi : i ≫ g = 0,
    { apply additive.cancel_zero_iff_epi.1 (abelian.to_im_epi f) _ _, exact gip, },
    let b := kernel.ι g,
    have hb : b ≫ g = 0 := kernel.condition _,
    have hgb : g b = 0 := comp_zero _ _ hb,
    cases h₂ _ hgb with a ha,
    cases quotient.exists_rep a with a' ha',
    rw ←ha' at ha,
    obtain ⟨Z, r, q, er, eq, comm⟩ := quotient.exact ha,
    rw ←f_factor f at comm,
    change r ≫ a'.2 ≫ p ≫ i = q ≫ b at comm,
    let P := pullback i b,
    let j : P ⟶ kernel g := pullback.snd,
    let c : P ⟶ kernel (cokernel.π f) := pullback.fst,
    let z : Z ⟶ P := pullback.lift (r ≫ a'.2 ≫ p) q (by simp only [category.assoc, comm]),
    have hjz : z ≫ j = q,
    { simp, refl, },
    have hcz : z ≫ c = r ≫ a'.2 ≫ p,
    { simp, refl, },
    haveI je : epi j := by { resetI, exact epi_of_epi_fac hjz, },
    have ji : is_iso j := mono_epi_iso j,
    have hh : c ≫ i = j ≫ b := pullback.condition,
    have hh' := congr_comp' hh (inv j),
    conv_rhs at hh' { rw ←category.assoc, rw is_iso.inv_hom_id, rw category.id_comp, },
    change b ≫ cokernel.π f = 0,
    rw ←hh',
    simp only [category.assoc],
    erw kernel.condition,
    rw ←category.assoc,
    rw has_zero_morphisms.comp_zero, }
end

lemma sub {P Q : C} (f : P ⟶ Q) (x y : pseudoelements P) : f x = f y →
  ∃ z, f z = 0 ∧ ∀ (R : C) (g : P ⟶ R), pseudo_apply g y = 0 → g z = g x :=
begin
  apply quotient.induction_on₂ x y,
  intros a a' h,
  obtain ⟨R, p, q, ep, eq, comm⟩ := quotient.exact h,
  change p ≫ (a.2 ≫ f) = q ≫ (a'.2 ≫ f) at comm,
  let a'' : R ⟶ P := p ≫ a.2 - q ≫ a'.2,
  use a'',
  split,
  { erw pseudo_apply_calc,
    change ⟦((p ≫ a.2 - q ≫ a'.2) ≫ f : with_codomain Q)⟧ = ⟦(0 : Q ⟶ Q)⟧,
    erw additive.preadditive.distrib_left,
    rw additive.neg_left,
    simp only [category.assoc],
    rw ←sub_eq_add_neg,
    rw sub_eq_zero.2 comm,
    apply zero_eq_zero, },
  { intros Z g hh,
    rw pseudo_apply_calc,
    erw pseudo_apply_calc,
    change ⟦(a'' ≫ g : with_codomain Z)⟧ = ⟦(a.2 ≫ g : with_codomain Z)⟧,
    change ⟦(a'.2 ≫ g : with_codomain Z)⟧ = ⟦(0 : Z ⟶ Z)⟧ at hh,
    obtain ⟨X, p', q', ep', eq', comm'⟩ := quotient.exact hh,
    change p' ≫ (a'.2 ≫ g) = q' ≫ 0 at comm',
    rw has_zero_morphisms.comp_zero at comm',
    have st := additive.cancel_zero_iff_epi.1 ep' _ (a'.snd ≫ g) comm',
    apply quotient.sound,
    use R,
    use 𝟙 R,
    use p,
    split,
    apply_instance,
    split,
    exact ep,
    change 𝟙 R ≫ a'' ≫ g = p ≫ a.2 ≫ g,
    rw category.id_comp,
    erw additive.preadditive.distrib_left,
    simp,
    rw st,
    erw has_zero_morphisms.comp_zero, }
end 

end

end category_theory.abelian