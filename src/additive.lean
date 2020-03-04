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

restate_axiom preadditive.distrib_left'
restate_axiom preadditive.distrib_right'

end

section preadditive
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables [preadditive.{v} C]

instance preadditive_hom_group {P Q : C} : add_comm_group (P ⟶ Q) := preadditive.hom_group.{v} P Q

def hom_right {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
mk' (λ g, f ≫ g) $ preadditive.distrib_right _ _ _ _ _

def hom_left (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
mk' (λ f, f ≫ g) $ λ f f', preadditive.distrib_left _ _ _ _ _ _ _

instance preadditive_has_zero_morphisms : has_zero_morphisms.{v} C :=
{ has_zero := infer_instance,
  comp_zero' := λ P Q f R, map_zero $ hom_right R f,
  zero_comp' := λ P Q R f, map_zero $ hom_left P f }

end preadditive

section opposite
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables [preadditive.{v} C]

-- Todo
-- Maybe we can use some properties of the opposite functor to make this less painful

end opposite

end category_theory.additive