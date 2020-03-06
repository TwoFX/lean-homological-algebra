import additive category_theory.limits.shapes.binary_products

universes v u

open category_theory
open category_theory.additive
open category_theory.limits

namespace category_theory.biproduct
variables {C : Type u} [𝒞 : category.{v} C] [preadditive.{v} C]
include 𝒞

structure biproduct_s (X Y : C) :=
(P : C)
(p₁ : P ⟶ X)
(p₂ : P ⟶ Y)
(s₁ : X ⟶ P)
(s₂ : Y ⟶ P)
(inv₁' : s₁ ≫ p₁ = 𝟙 X . obviously)
(inv₂' : s₂ ≫ p₂ = 𝟙 Y . obviously)
(van₁' : s₂ ≫ p₁ = 0 . obviously)
(van₂' : s₁ ≫ p₂ = 0 . obviously)
(total' : p₁ ≫ s₁ + p₂ ≫ s₂ = 𝟙 P . obviously)

restate_axiom biproduct_s.inv₁'
restate_axiom biproduct_s.inv₂'
restate_axiom biproduct_s.van₁'
restate_axiom biproduct_s.van₂'
restate_axiom biproduct_s.total'
attribute [simp, reassoc] biproduct_s.inv₁ biproduct_s.inv₂ biproduct_s.van₁ biproduct_s.van₂
attribute [simp] biproduct_s.total

section
variable (C)

class has_biproducts :=
(biproduct : Π (X Y : C), biproduct_s.{v} X Y)

end

def biproduct.of_prod (X Y : C) [has_limit.{v} (pair X Y)] : biproduct_s.{v} X Y :=
{ P := X ⨯ Y,
  p₁ := @category_theory.limits.prod.fst _ _ X Y _,
  p₂ := @category_theory.limits.prod.snd _ _ X Y _,
  s₁ := prod.lift (𝟙 X) 0,
  s₂ := prod.lift 0 (𝟙 Y),
  total' :=
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

instance [has_binary_products.{v} C] : has_biproducts.{v} C :=
{ biproduct := λ X Y, biproduct.of_prod X Y }

section has_biproducts
variables [has_biproducts.{v} C]

abbreviation biproduct (X Y : C) := biproduct_s.P (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.p₁ (X Y : C) := biproduct_s.p₁ (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.p₂ (X Y : C) := biproduct_s.p₂ (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.s₁ (X Y : C) := biproduct_s.s₁ (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.s₂ (X Y : C) := biproduct_s.s₂ (has_biproducts.biproduct.{v} X Y)

def out {X Y T : C} (f : X ⟶ T) (g : Y ⟶ T) : biproduct X Y ⟶ T :=
biproduct.p₁ X Y ≫ f + biproduct.p₂ X Y ≫ g

@[simp] lemma s₁_out {X Y T : C} {f : X ⟶ T} {g : Y ⟶ T} : biproduct.s₁ X Y ≫ out f g = f :=
by unfold out; simp

@[simp] lemma s₂_out {X Y T : C} {f : X ⟶ T} {g : Y ⟶ T} : biproduct.s₂ X Y ≫ out f g = g :=
by unfold out; simp

end has_biproducts

end category_theory.biproduct