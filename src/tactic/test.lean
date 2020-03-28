import tactic.commutativity
import category_theory.category
import pseudoelements

open category_theory
open category_theory.abelian
open category_theory.abelian.pseudoelements


universes v u
section
variables {V : Type u} [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun
section four
variables {A B C D A' B' C' D' : V}
variables {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
variables {f' : A' ⟶ B'} {g' : B' ⟶ C'} {h' : C' ⟶ D'}
variables {α : A ⟶ A'} {β : B ⟶ B'} {γ : C ⟶ C'} {δ : D ⟶ D'}
variables (fg : exact f g) (gh : exact g h) (fg' : exact f' g') (gh' : exact g' h')
variables (comm₁ : α ≫ f' = f ≫ β) (comm₂ : β ≫ g' = g ≫ γ) (comm₃ : γ ≫ h' = h ≫ δ)
include fg gh fg' gh' comm₁ comm₂ comm₃

set_option trace.app_builder true


lemma test (a : A) (b : B) (h₀ : β b = 0) (h₁ : f a = b) : f' (α a) = 0 :=
begin
  --to_zero (y (u (g (f a)))),
  commutativity,
end
#print test


end four

end
