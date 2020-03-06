import category_theory.category
import algebra.group.hom
import data.opposite
import category_theory.opposites
import category_theory.limits.shapes.zero

universes v u

open category_theory
open category_theory.limits
open opposite
open add_monoid_hom

namespace category_theory.additive
section
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

class preadditive :=
(hom_group : Π P Q : C, add_comm_group (P ⟶ Q))
(distrib_left' : Π P Q R : C, ∀ (f f' : P ⟶ Q) (g : Q ⟶ R),
  (f + f') ≫ g = f ≫ g + f' ≫ g . obviously)
(distrib_right' : Π P Q R : C, ∀ (f : P ⟶ Q) (g g' : Q ⟶ R),
  f ≫ (g + g') = f ≫ g + f ≫ g' . obviously)

attribute [instance] preadditive.hom_group
restate_axiom preadditive.distrib_left'
restate_axiom preadditive.distrib_right'
attribute [simp] preadditive.distrib_left
attribute [simp] preadditive.distrib_right

end

section preadditive
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables [preadditive.{v} C]

def hom_right {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
mk' (λ g, f ≫ g) $ preadditive.distrib_right _ _ _ _ _

def hom_left (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
mk' (λ f, f ≫ g) $ λ f f', preadditive.distrib_left _ _ _ _ _ _ _

instance preadditive_has_zero_morphisms : has_zero_morphisms.{v} C :=
{ has_zero := infer_instance,
  comp_zero' := λ P Q f R, map_zero $ hom_right R f,
  zero_comp' := λ P Q R f, map_zero $ hom_left P f }

lemma cancel_zero_iff_mono {Q R : C} {f : Q ⟶ R} : mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
iff.intro (λ m P g, @zero_of_comp_mono _ _ _ _ _ _ _ _ m) $ λ h,
⟨λ P g g' hg, sub_eq_zero.1 $ h P _ $ eq.trans (map_sub (hom_left P f) g g') (sub_eq_zero.2 hg)⟩

lemma cancel_zero_iff_epi {P Q : C} {f : P ⟶ Q} : epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
iff.intro (λ e R g, @zero_of_comp_epi _ _ _ _ _ _ _ _ e) $ λ h,
⟨λ R g g' hg, sub_eq_zero.1 $ h R _ $ eq.trans (map_sub (hom_right R f) g g') (sub_eq_zero.2 hg)⟩

end preadditive

section opposite
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables [preadditive.{v} C]

-- Todo
-- Maybe we can use some properties of the opposite functor to make this less painful

end opposite

end category_theory.additive