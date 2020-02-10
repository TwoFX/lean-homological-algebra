import additive category_theory.limits.shapes.binary_products

universes v u

open category_theory
open category_theory.additive
open category_theory.limits

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

lemma product.unique {X Y P : C} [l : has_limit.{v} (pair X Y)] {f g : P ⟶ X ⨯ Y}
    (h₁ : f ≫ (@category_theory.limits.prod.fst _ _ X Y _) = g ≫ (@category_theory.limits.prod.fst _ _ X Y _))
    (h₂ : f ≫ (@category_theory.limits.prod.snd _ _ X Y _) = g ≫ (@category_theory.limits.prod.snd _ _ X Y _)) :
    f = g :=
begin
  let fan := binary_fan.mk (f ≫ (@category_theory.limits.prod.fst _ _ X Y _)) (f ≫ (@category_theory.limits.prod.snd _ _ X Y _)),
  have hf : f = l.is_limit.lift fan :=
  begin
    refine l.is_limit.uniq fan f _,
    intro j,
    cases j,
    { rw binary_fan.mk_π_app_left, refl, },
    { rw binary_fan.mk_π_app_right, refl, }
  end,
  have hg : g = l.is_limit.lift fan :=
  begin
    refine l.is_limit.uniq fan g _,
    intro j,
    cases j,
    { rw binary_fan.mk_π_app_left, rw h₁, refl, },
    { rw binary_fan.mk_π_app_right, rw h₂, refl, }
  end,
  rw [hf, hg],
end

end

namespace category_theory.biproduct
variables {C : Type u} [𝒞 : preadditive_category.{v} C]
include 𝒞

structure biproduct (X Y : C) :=
(P : C)
(p₁ : P ⟶ X)
(p₂ : P ⟶ Y)
(s₁ : X ⟶ P)
(s₂ : Y ⟶ P)
(inv₁ : s₁ ≫ p₁ = 𝟙 X)
(inv₂ : s₂ ≫ p₂ = 𝟙 Y)
(van₁ : s₂ ≫ p₁ = 0)
(van₂ : s₁ ≫ p₂ = 0)
(total : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 P)

notation X ` ⊕c `:20 Y:20 := (biproduct X Y).P

lemma biproduct.from_prod (X Y : C) [has_limit.{v} (pair X Y)] : biproduct.{v} X Y :=
{ P := X ⨯ Y,
  p₁ := @category_theory.limits.prod.fst _ _ X Y _,
  p₂ := @category_theory.limits.prod.snd _ _ X Y _,
  s₁ := prod.lift (𝟙 X) 0,
  s₂ := prod.lift 0 (𝟙 Y),
  inv₁ := by tidy,
  inv₂ := by tidy,
  van₁ := by tidy,
  van₂ := by tidy,
  total := begin
    let p₁ := @category_theory.limits.prod.fst _ _ X Y _,
    let p₂ := @category_theory.limits.prod.snd _ _ X Y _,
    let s₁ := prod.lift (𝟙 X) (0 : X ⟶ Y),
    let s₂ := prod.lift (0 : Y ⟶ X) (𝟙 Y),
    have inv₁ : s₁ ≫ p₁ = 𝟙 X := by tidy,
    have inv₂ : s₂ ≫ p₂ = 𝟙 Y := by tidy,
    have van₁ : s₂ ≫ p₁ = 0 := by tidy,
    have van₂ : s₁ ≫ p₂ = 0 := by tidy,
    have h₁ : (p₁ ≫ s₁ + p₂ ≫ s₂) ≫ p₁ = p₁,
    begin
      rw [distrib_left, category.assoc, inv₁, category.assoc],
      rw [van₁, category.comp_id, comp_zero, add_right_eq_self]
    end,
    have h₂ : (p₁ ≫ s₁ + p₂ ≫ s₂) ≫ p₂ = p₂,
    begin
      rw [distrib_left, category.assoc, van₂, category.assoc],
      rw [inv₂, category.comp_id, comp_zero, add_left_eq_self],
    end,
    refine product.unique _ _,
    { rw category.id_comp, exact h₁ },
    { rw category.id_comp, exact h₂ },
  end
}

end category_theory.biproduct