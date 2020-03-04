import additive category_theory.limits.shapes.binary_products

universes v u

open category_theory
open category_theory.additive
open category_theory.limits

namespace category_theory.biproduct
variables {C : Type u} [𝒞 : category.{v} C] [preadditive.{v} C]
include 𝒞

structure biproduct (X Y : C) :=
(P : C)
(p₁ : P ⟶ X)
(p₂ : P ⟶ Y)
(s₁ : X ⟶ P)
(s₂ : Y ⟶ P)
(inv₁ : s₁ ≫ p₁ = 𝟙 X . obviously)
(inv₂ : s₂ ≫ p₂ = 𝟙 Y . obviously)
(van₁ : s₂ ≫ p₁ = 0 . obviously)
(van₂ : s₁ ≫ p₂ = 0 . obviously)
(total : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 P . obviously)

notation X ` ⊕c `:20 Y:20 := (biproduct X Y).P

def biproduct.of_prod (X Y : C) [has_limit.{v} (pair X Y)] : biproduct.{v} X Y :=
{ P := X ⨯ Y,
  p₁ := @category_theory.limits.prod.fst _ _ X Y _,
  p₂ := @category_theory.limits.prod.snd _ _ X Y _,
  s₁ := prod.lift (𝟙 X) 0,
  s₂ := prod.lift 0 (𝟙 Y),
  total :=
  begin
    ext j,
    cases j;
    rw [preadditive.distrib_left, category.assoc, category.assoc];
    simp,
    { rw has_zero_morphisms.comp_zero _ category_theory.limits.prod.snd X,
      refl, },
    { rw has_zero_morphisms.comp_zero _ category_theory.limits.prod.fst Y,
      refl, },
  end
}

end category_theory.biproduct