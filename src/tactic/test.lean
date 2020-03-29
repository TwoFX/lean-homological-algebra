import tactic.commutativity
import category_theory.category
import pseudoelements
import tactic.diagram_chase

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

set_option profiler true

lemma four (hα : epi α) (hβ : mono β) (hδ : mono δ) : mono γ :=
begin
  apply mono_of_zero_of_map_zero,
  intros c hc,
  chase c using [g, β, f', α] with b b' a' a,
  have : f a = b, by commutativity,
  commutativity,
end

#print four

end four

section
variables {A B C D E : V} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (α : A ⟶ E) (β : E ⟶ D)

lemma l (c : f ≫ g ≫ h = α ≫ β) (a : A) : h (g (f a)) = β (α a) :=
begin
  commutativity,
end


end

end
