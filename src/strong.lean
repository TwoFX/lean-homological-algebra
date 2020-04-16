/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import category_theory.limits.shapes.regular_mono
import category_theory.comma

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variables {C}

@[ext]
class has_lift {f g : arrow C} (sq : f ⟶ g) :=
(lift : f.right ⟶ g.left)
(fac_left : f.hom ≫ lift = sq.left)
(fac_right : lift ≫ g.hom = sq.right)

attribute [simp, reassoc] has_lift.fac_left has_lift.fac_right

abbreviation lift {f g : arrow C} (sq : f ⟶ g) [has_lift sq] : f.right ⟶ g.left :=
has_lift.lift sq

lemma lift.fac_left {f g : arrow C} (sq : f ⟶ g) [has_lift sq] : f.hom ≫ lift sq = sq.left :=
by simp

lemma lift.fac_right {f g : arrow C} (sq : f ⟶ g) [has_lift sq] : lift sq ≫ g.hom = sq.right :=
by simp

@[simp, reassoc]
lemma lift_mk'_left {X Y P Q : C} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (h : u ≫ g = f ≫ v) [has_lift $ arrow.hom_mk' h] : f ≫ lift (arrow.hom_mk' h) = u :=
by simp only [←arrow.mk_hom f, lift.fac_left, arrow.hom_mk'_left]

@[simp, reassoc]
lemma lift_mk'_right {X Y P Q : C} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (h : u ≫ g = f ≫ v) [has_lift $ arrow.hom_mk' h] : lift (arrow.hom_mk' h) ≫ g = v :=
by simp only [←arrow.mk_hom g, lift.fac_right, arrow.hom_mk'_right]

section

instance subsingleton_lift_of_epi {f g : arrow C} (sq : f ⟶ g) [epi f.hom] :
  subsingleton (has_lift sq) :=
subsingleton.intro $ λ a b, has_lift.ext a b $ (cancel_epi f.hom).1 $ by simp

instance subsingleton_lifting_of_mono {f g : arrow C} (sq : f ⟶ g) [mono g.hom] :
  subsingleton (has_lift sq) :=
subsingleton.intro $ λ a b, has_lift.ext a b $ (cancel_mono g.hom).1 $ by simp

end

variables {P Q : C} (f : P ⟶ Q)

class strong_epi :=
(epi : epi f)
(has_lift : Π {X Y : C} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y} [mono.{v} z] (h : u ≫ z = f ≫ v),
  has_lift $ arrow.hom_mk' h)

attribute [instance] strong_epi.has_lift

@[priority 100]
instance epi_of_strong_epi [strong_epi f] : epi f := strong_epi.epi

section
variables {R : C} (g : Q ⟶ R) [epi f] [epi g]

def strong_epi_comp [strong_epi f] [strong_epi g] : strong_epi (f ≫ g) :=
{ epi := epi_comp _ _,
  has_lift :=
  begin
    introsI,
    have h₀ : u ≫ z = f ≫ g ≫ v, by simpa [category.assoc] using h,
    let w : Q ⟶ X := lift (arrow.hom_mk' h₀),
    have h₁ : w ≫ z = g ≫ v, by rw lift_mk'_right,
    exact ⟨(lift (arrow.hom_mk' h₁) : R ⟶ X), by simp, by simp⟩
  end }

end

section
variables {R : C} (g : Q ⟶ R) [epi (f ≫ g)]

def strong_epi_of_strong_epi_comp [strong_epi (f ≫ g)] : strong_epi g :=
{ epi := epi_of_epi f g,
  has_lift :=
  begin
    introsI,
    have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v, by simp only [category.assoc, h],
    exact ⟨(lift (arrow.hom_mk' h₀) : R ⟶ X), (cancel_mono z).1 (by simp [h]), by simp⟩,
  end }

end

def mono_strong_epi_is_iso [strong_epi f] [mono f] : is_iso f :=
{ inv := lift $ arrow.hom_mk' $ show 𝟙 P ≫ f = f ≫ 𝟙 Q, by simp }

local attribute [reassoc] regular_epi.w

def regular_epi.lift' {W X Y : C} (f : X ⟶ Y) [regular_epi f] (k : X ⟶ W)
  (h : (regular_epi.left : regular_epi.W f ⟶ X) ≫ k = regular_epi.right ≫ k) :
  {l : Y ⟶ W // f ≫ l = k} :=
cofork.is_colimit.desc' (regular_epi.is_colimit) _ h

instance strong_epi_of_regular_epi [regular_epi f] : strong_epi f :=
{ epi := by apply_instance,
  has_lift :=
  begin
    introsI,
    have : (regular_epi.left : regular_epi.W f ⟶ P) ≫ u = regular_epi.right ≫ u,
    { apply (cancel_mono z).1,
      simp only [category.assoc, h, regular_epi.w_assoc] },
    obtain ⟨t, ht⟩ := regular_epi.lift' f u this,
    exact ⟨t, ht, (cancel_epi f).1
      (by simp only [←category.assoc, ht, ←h, arrow.mk_hom, arrow.hom_mk'_right])⟩,
  end }

end category_theory
