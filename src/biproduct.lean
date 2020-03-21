/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import additive category_theory.limits.shapes.binary_products
import hom_to_mathlib

universes v u

open category_theory
open category_theory.preadditive
open category_theory.limits

namespace category_theory.limits
variables {C : Type u} [𝒞 : category.{v} C] [preadditive.{v} C]
include 𝒞

class is_biproduct (X Y P : C) :=
(fst : P ⟶ X)
(snd : P ⟶ Y)
(inl : X ⟶ P)
(inr : Y ⟶ P)
(inl_fst' : inl ≫ fst = 𝟙 X . obviously)
(inr_snd' : inr ≫ snd = 𝟙 Y . obviously)
(inr_fst' : inr ≫ fst = 0 . obviously)
(inl_snd' : inl ≫ snd = 0 . obviously)
(total' : fst ≫ inl + snd ≫ inr = 𝟙 P . obviously)

restate_axiom is_biproduct.inl_fst'
restate_axiom is_biproduct.inr_snd'
restate_axiom is_biproduct.inr_fst'
restate_axiom is_biproduct.inl_snd'
restate_axiom is_biproduct.total'
attribute [simp, reassoc] is_biproduct.inl_fst is_biproduct.inr_snd is_biproduct.inr_fst is_biproduct.inl_snd
attribute [simp] is_biproduct.total'

class has_biproduct (X Y : C) :=
(P : C)
(is_biproduct : is_biproduct.{v} X Y P)

attribute [instance] has_biproduct.is_biproduct

section has_biproduct
variables {X Y : C} [has_biproduct.{v} X Y]

section
variables (X Y)
abbreviation biproduct := has_biproduct.P.{v} X Y

notation X ` ⊞ `:20 Y:20 := biproduct X Y
end

abbreviation biproduct.fst := (has_biproduct.is_biproduct.{v} X Y).fst
abbreviation biproduct.snd := (has_biproduct.is_biproduct.{v} X Y).snd
abbreviation biproduct.inl := (has_biproduct.is_biproduct.{v} X Y).inl
abbreviation biproduct.inr := (has_biproduct.is_biproduct.{v} X Y).inr
abbreviation biproduct.inl_fst := is_biproduct.inl_fst.{v} X Y (biproduct X Y)
abbreviation biproduct.inr_snd := is_biproduct.inr_snd.{v} X Y (biproduct X Y)
abbreviation biproduct.inr_fst := is_biproduct.inr_fst.{v} X Y (biproduct X Y)
abbreviation biproduct.inl_snd := is_biproduct.inl_snd.{v} X Y (biproduct X Y)
abbreviation biproduct.total := is_biproduct.total.{v} X Y (biproduct X Y)

instance fst_epi : epi (biproduct.fst : X ⊞ Y ⟶ X) :=
epi_of_epi_fac biproduct.inl_fst

instance snd_epi : epi (biproduct.snd : X ⊞ Y ⟶ Y) :=
epi_of_epi_fac biproduct.inr_snd

instance inl_mono : mono (biproduct.inl : X ⟶ X ⊞ Y) :=
mono_of_mono_fac biproduct.inl_fst

instance inr_mono : mono (biproduct.inr : Y ⟶ X ⊞ Y) :=
mono_of_mono_fac biproduct.inr_snd

def biproduct.lift {T : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊞ Y :=
f ≫ biproduct.inl + g ≫ biproduct.inr

@[simp] lemma biproduct.lift_fst {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biproduct.lift f g ≫ biproduct.fst = f :=
by unfold biproduct.lift; simp

@[simp] lemma biproduct.lift_snd {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biproduct.lift f g ≫ biproduct.snd = g :=
by unfold biproduct.lift; simp

section
variables (X Y)

def biproduct.cone : binary_fan X Y :=
binary_fan.mk biproduct.fst biproduct.snd

def biproduct.cone_is_limit : is_limit $ biproduct.cone X Y :=
{ lift := λ s, biproduct.lift (s.π.app walking_pair.left) (s.π.app walking_pair.right),
  fac' := λ s j, by { cases j, erw biproduct.lift_fst, erw biproduct.lift_snd },
  uniq' := λ s m h, by erw [←category.comp_id _ m, ←biproduct.total, preadditive.distrib_right,
    ←category.assoc, ←category.assoc, h walking_pair.left, h walking_pair.right]; refl }

end

@[ext] lemma biproduct.ext_lift {T : C} (f g : T ⟶ X ⊞ Y)
  (h₁ : f ≫ biproduct.fst = g ≫ biproduct.fst) (h₂ : f ≫ biproduct.snd = g ≫ biproduct.snd) : f = g :=
is_limit.hom_ext (biproduct.cone_is_limit X Y) $ λ j, by { cases j, exact h₁, exact h₂ }

def biproduct.desc {T : C} (f : X ⟶ T) (g : Y ⟶ T) : X ⊞ Y ⟶ T :=
biproduct.fst ≫ f + biproduct.snd ≫ g

@[simp] lemma biproduct.inl_desc {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biproduct.inl ≫ biproduct.desc f g = f :=
by unfold biproduct.desc; simp

@[simp] lemma biproduct.inr_desc {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biproduct.inr ≫ biproduct.desc f g = g :=
by unfold biproduct.desc; simp

section
variables (X Y)

def biproduct.cocone : binary_cofan X Y :=
binary_cofan.mk biproduct.inl biproduct.inr

def biproduct.cocone_is_colimit : is_colimit $ biproduct.cocone X Y :=
{ desc := λ s, biproduct.desc (s.ι.app walking_pair.left) (s.ι.app walking_pair.right),
  fac' := λ s j, by { cases j, erw biproduct.inl_desc, erw biproduct.inr_desc },
  uniq' := λ s m h, by erw [←category.id_comp _ m, ←biproduct.total, preadditive.distrib_left,
    category.assoc, category.assoc, h walking_pair.left, h walking_pair.right]; refl }

end

@[ext] lemma biproduct.ext_desc {T : C} {f g : X ⊞ Y ⟶ T}
  (h₁ : biproduct.inl ≫ f = biproduct.inl ≫ g) (h₂ : biproduct.inr ≫ f = biproduct.inr ≫ g) : f = g :=
is_colimit.hom_ext (biproduct.cocone_is_colimit X Y) $ λ j, by { cases j, exact h₁, exact h₂ }

section
variables {Z : C} (f : Z ⟶ X) (g : Z ⟶ Y)

instance mono_lift_of_mono_f [mono f] : mono (biproduct.lift f g) :=
mono_of_mono_fac biproduct.lift_fst

instance mono_lift_of_mono_g [mono g] : mono (biproduct.lift f g) :=
mono_of_mono_fac biproduct.lift_snd

end

section
variables {Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

instance epi_desc_of_epi_f [epi f] : epi (biproduct.desc f g) :=
epi_of_epi_fac biproduct.inl_desc

instance epi_desc_of_epi_g [epi g] : epi (biproduct.desc f g) :=
epi_of_epi_fac biproduct.inr_desc

end

end has_biproduct

section has_biproducts

section
variable (C)

class has_biproducts :=
(has_biproduct : Π (X Y : C), has_biproduct.{v} X Y)

attribute [instance] has_biproducts.has_biproduct

end

def biproduct.of_prod (X Y : C) [has_limit.{v} (pair X Y)] : has_biproduct.{v} X Y :=
{ P := X ⨯ Y,
  is_biproduct :=
  { fst := @category_theory.limits.prod.fst _ _ X Y _,
    snd := @category_theory.limits.prod.snd _ _ X Y _,
    inl := prod.lift (𝟙 X) 0,
    inr := prod.lift 0 (𝟙 Y),
    total' :=
    begin
      ext j,
      cases j;
      simp;
      erw has_zero_morphisms.comp_zero,
    end } }

@[priority 100]
instance [has_binary_products.{v} C] : has_biproducts.{v} C :=
{ has_biproduct := λ X Y, biproduct.of_prod X Y }

end has_biproducts

end category_theory.limits
