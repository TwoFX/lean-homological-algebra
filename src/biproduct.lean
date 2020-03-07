import additive category_theory.limits.shapes.binary_products

universes v u

open category_theory
open category_theory.additive
open category_theory.limits

namespace category_theory.limits
variables {C : Type u} [𝒞 : category.{v} C] [preadditive.{v} C]
include 𝒞

structure biproduct_s (X Y : C) :=
(P : C)
(π₁ : P ⟶ X)
(π₂ : P ⟶ Y)
(ι₁ : X ⟶ P)
(ι₂ : Y ⟶ P)
(ι₁_π₁' : ι₁ ≫ π₁ = 𝟙 X . obviously)
(ι₂_π₂' : ι₂ ≫ π₂ = 𝟙 Y . obviously)
(ι₂_π₁' : ι₂ ≫ π₁ = 0 . obviously)
(ι₁_π₂' : ι₁ ≫ π₂ = 0 . obviously)
(π_ι' : π₁ ≫ ι₁ + π₂ ≫ ι₂ = 𝟙 P . obviously)

restate_axiom biproduct_s.ι₁_π₁'
restate_axiom biproduct_s.ι₂_π₂'
restate_axiom biproduct_s.ι₂_π₁'
restate_axiom biproduct_s.ι₁_π₂'
restate_axiom biproduct_s.π_ι'
attribute [simp, reassoc] biproduct_s.ι₁_π₁ biproduct_s.ι₂_π₂ biproduct_s.ι₂_π₁ biproduct_s.ι₁_π₂
attribute [simp] biproduct_s.π_ι'

section
variable (C)

class has_biproducts :=
(biproduct : Π (X Y : C), biproduct_s.{v} X Y)

end

def biproduct.of_prod (X Y : C) [has_limit.{v} (pair X Y)] : biproduct_s.{v} X Y :=
{ P := X ⨯ Y,
  π₁ := @category_theory.limits.prod.fst _ _ X Y _,
  π₂ := @category_theory.limits.prod.snd _ _ X Y _,
  ι₁ := prod.lift (𝟙 X) 0,
  ι₂ := prod.lift 0 (𝟙 Y),
  π_ι' :=
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
abbreviation biproduct.π₁ {X Y : C} := biproduct_s.π₁ (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.π₂ {X Y : C} := biproduct_s.π₂ (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.ι₁ {X Y : C} := biproduct_s.ι₁ (has_biproducts.biproduct.{v} X Y)
abbreviation biproduct.ι₂ {X Y : C} := biproduct_s.ι₂ (has_biproducts.biproduct.{v} X Y)

def biproduct.lift {X Y T : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ biproduct X Y :=
f ≫ biproduct.ι₁ + g ≫ biproduct.ι₂

@[simp] lemma biproduct.lift_π₁ {X Y T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biproduct.lift f g ≫ biproduct.π₁ = f :=
by unfold biproduct.lift; simp

@[simp] lemma biproduct.lift_π₂ {X Y T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biproduct.lift f g ≫ biproduct.π₂ = g :=
by unfold biproduct.lift; simp

def biproduct.cone (X Y : C) : binary_fan X Y :=
binary_fan.mk biproduct.π₁ biproduct.π₂

def biproduct.cone_is_limit (X Y : C) : is_limit $ biproduct.cone X Y :=
{ lift := λ s, biproduct.lift (s.π.app walking_pair.left) (s.π.app walking_pair.right),
  fac' := λ s j, by { cases j, erw biproduct.lift_π₁, erw biproduct.lift_π₂ },
  uniq' := λ s m h, by erw [←category.comp_id _ m, ←biproduct_s.π_ι, preadditive.distrib_right,
    ←category.assoc, ←category.assoc, h walking_pair.left, h walking_pair.right]; refl }

@[ext] lemma biproduct.ext_lift {X Y T : C} (f g : T ⟶ biproduct X Y)
  (h₁ : f ≫ biproduct.π₁ = g ≫ biproduct.π₁) (h₂ : f ≫ biproduct.π₂ = g ≫ biproduct.π₂) : f = g :=
is_limit.hom_ext (biproduct.cone_is_limit X Y) $ λ j, by { cases j, exact h₁, exact h₂ }

def biproduct.desc {X Y T : C} (f : X ⟶ T) (g : Y ⟶ T) : biproduct X Y ⟶ T :=
biproduct.π₁ ≫ f + biproduct.π₂ ≫ g

@[simp] lemma biproduct.ι₁_desc {X Y T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biproduct.ι₁ ≫ biproduct.desc f g = f :=
by unfold biproduct.desc; simp

@[simp] lemma biproduct.ι₂_desc {X Y T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biproduct.ι₂ ≫ biproduct.desc f g = g :=
by unfold biproduct.desc; simp

def biproduct.cocone (X Y : C) : binary_cofan X Y :=
binary_cofan.mk biproduct.ι₁ biproduct.ι₂

def biproduct.cocone_is_colimit (X Y : C) : is_colimit $ biproduct.cocone X Y :=
{ desc := λ s, biproduct.desc (s.ι.app walking_pair.left) (s.ι.app walking_pair.right),
  fac' := λ s j, by { cases j, erw biproduct.ι₁_desc, erw biproduct.ι₂_desc },
  uniq' := λ s m h, by erw [←category.id_comp _ m, ←biproduct_s.π_ι, preadditive.distrib_left,
    category.assoc, category.assoc, h walking_pair.left, h walking_pair.right]; refl }

@[ext] lemma biproduct.ext_desc {X Y T : C} {f g : biproduct X Y ⟶ T}
  (h₁ : biproduct.ι₁ ≫ f = biproduct.ι₁ ≫ g) (h₂ : biproduct.ι₂ ≫ f = biproduct.ι₂ ≫ g) : f = g :=
is_colimit.hom_ext (biproduct.cocone_is_colimit X Y) $ λ j, by { cases j, exact h₁, exact h₂ }

end has_biproducts

end category_theory.limits
