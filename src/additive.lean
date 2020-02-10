import category_theory.category algebra.group.hom data.opposite category_theory.opposites

universes v u

open category_theory
open opposite

namespace category_theory.additive
section
variables (C : Type u)

class preadditive_category extends category.{v} C :=
(hom_group : Π P Q : C, add_comm_group (P ⟶ Q))
(compose_hom_left' : Π P Q R : C, ∀ (g : Q ⟶ R), is_add_group_hom (λ (f : P ⟶ Q), f ≫ g) . obviously)
(compose_hom_right' : Π P Q R : C, ∀ (f : P ⟶ Q), is_add_group_hom (λ (g : Q ⟶ R), f ≫ g) . obviously)

restate_axiom preadditive_category.compose_hom_left'
restate_axiom preadditive_category.compose_hom_right'
end

section
variables (C : Type u) [𝒞 : preadditive_category.{v} C]
include 𝒞

instance hom_group (P Q : C) : add_comm_group (P ⟶ Q) := preadditive_category.hom_group P Q



instance op_preadd : @preadditive_category.{v} Cᵒᵖ :=
{ hom := category.opposite.hom,
  id := _,
  comp := _,
  id_comp' := category.opposite.id_comp',
  comp_id' := category.opposite.comp_id',
  assoc' := category.opposite.assoc',
  hom_group := λ P Q, 
  begin
    exact {
      add := λ f g, (f.unop + g.unop).op,
      add_assoc := by tidy,
      zero := (0 : (unop Q) ⟶ (unop P)).op,
      zero_add := by tidy,
      add_zero := λ f, begin
        unfold has_add.add,
        unfold add_semigroup.add,
        rw [has_hom.hom.unop_op, add_zero, has_hom.hom.op_unop]
      end,
      neg := λ f, (-f.unop).op,
      add_left_neg := λ f, begin
        unfold has_add.add,
        unfold add_semigroup.add,
        unfold add_monoid.add,
        unfold has_neg.neg,
        rw [has_hom.hom.unop_op],
        have : add_group.neg (has_hom.hom.unop f) = -(has_hom.hom.unop f) := rfl,
        rw this,
        rw add_left_neg,
        refl,
      end,
      add_comm := λ f g, begin

        unfold has_add.add,
        unfold add_semigroup.add,
        rw add_comm,
      end }
      end,
  compose_hom_left' := λ P Q R g, { map_add := λ f f', begin
    unfold has_add.add,
    unfold add_semigroup.add,
    unfold add_monoid.add,
    unfold add_group.add,
    unfold add_comm_group.add,
    rw ←@has_hom.hom.op_unop _ _ _ _ g,
    rw ←op_comp,
    apply congr_arg has_hom.hom.op,
    simp only [has_hom.hom.op_unop, unop_comp],
    have h := (preadditive_category.compose_hom_right _ _ _ (unop P) g.unop).map_add,
    exact h f.unop f'.unop,
  end },
  compose_hom_right' := λ P Q R f, { map_add := λ g g', begin
    unfold has_add.add,
    unfold add_semigroup.add,
    unfold add_monoid.add,
    unfold add_group.add,
    unfold add_comm_group.add,
    rw ←@has_hom.hom.op_unop _ _ _ _ f,
    rw ←op_comp,
    apply congr_arg has_hom.hom.op,
    simp only [has_hom.hom.op_unop, unop_comp],
    have h := (preadditive_category.compose_hom_left _ (unop R) _ _ f.unop).map_add,
    exact h g.unop g'.unop,
  end} }

end
end category_theory.additive