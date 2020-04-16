
/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.category
import strong

open category_theory

universes v u

namespace category_theory.epi_mono
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

section
variables {X Y : C} (f : X ⟶ Y)

structure SEMF :=
{I : C}
(p : X ⟶ I)
(i : I ⟶ Y)
(fac : p ≫ i = f)
[i_mono : mono i]
[p_strong_epi : strong_epi p]

attribute [instance] SEMF.i_mono
attribute [instance] SEMF.p_strong_epi

def SEMF.unique (g h : SEMF f) : g.I ≅ h.I :=
begin
  have : g.p ≫ g.i = h.p ≫ h.i,
  { rw g.fac, rw h.fac, },
  let u : g.I ⟶ h.I := lifting.lift (lifting_problem.mk this),
  let v : h.I ⟶ g.I := lifting.lift (lifting_problem.mk this.symm),
  refine ⟨u, v, _, _⟩,
  { rw auto_param_eq,
    apply (cancel_epi g.p).1,
    apply (cancel_mono g.i).1,
    rw ←category.assoc,
    rw has_solution.fac_left (lifting_problem.mk this),
    rw category.assoc,
    rw has_solution.fac_right (lifting_problem.mk this.symm),
    simp only [category.assoc, g.fac, h.fac, category.id_comp], },
  { rw auto_param_eq,
    apply (cancel_epi h.p).1,
    apply (cancel_mono h.i).1,
    rw ←category.assoc,
    rw has_solution.fac_left (lifting_problem.mk this.symm),
    rw category.assoc,
    rw has_solution.fac_right (lifting_problem.mk this),
    simp only [category.assoc, g.fac, h.fac, category.id_comp], }
end

lemma SEMF.unique_fac_left (g h : SEMF f) : g.p ≫ (SEMF.unique f g h).hom = h.p :=
begin
  have : g.p ≫ g.i = h.p ≫ h.i,
  { rw g.fac, rw h.fac, },
  erw has_solution.fac_left (lifting_problem.mk this),
end

lemma SEMF.unique_fac_right (g h : SEMF f) :
  (SEMF.unique f g h).hom ≫ h.i = g.i :=
begin
  have : g.p ≫ g.i = h.p ≫ h.i,
  { rw g.fac, rw h.fac, },
  erw has_solution.fac_right (lifting_problem.mk this),
end

end

section
variables {X Y : C} (f : X ⟶ Y)

class has_SEMF :=
(SEMF : SEMF f)

end

section
variable (C)

class has_SEMFs :=
(has_SEMF : Π {X Y : C} (f : X ⟶ Y), has_SEMF.{v} f)

attribute [instance] has_SEMFs.has_SEMF

end

section

variables [has_SEMFs.{v} C]
variables {W X Y Z : C} {f : W ⟶ X} (s : SEMF f) {g : Y ⟶ Z}
  (t : SEMF g) {h : W ⟶ Y} {i : X ⟶ Z} (w : f ≫ i = h ≫ g)

include w

def SEMF.lower : SEMF (f ≫ i) :=
{ I := _,
  p := (has_SEMF.SEMF (h ≫ t.p)).p,
  i := (has_SEMF.SEMF (h ≫ t.p)).i ≫ t.i,
  fac := by rw [←category.assoc, SEMF.fac, category.assoc, SEMF.fac, w],
  i_mono := by apply_instance,
  p_strong_epi := by apply_instance }

def SEMF.upper : SEMF (f ≫ i) :=
{ I := _,
  p := s.p ≫ (has_SEMF.SEMF (s.i ≫ i)).p,
  i := (has_SEMF.SEMF (s.i ≫ i)).i,
  fac := by rw [category.assoc, SEMF.fac, ←category.assoc, SEMF.fac],
  i_mono := by apply_instance,
  p_strong_epi := by apply_instance }

def SEMF.nat_hom : s.I ⟶ t.I :=
(has_SEMF.SEMF (s.i ≫ i)).p ≫ (SEMF.unique _ (SEMF.upper s w) (SEMF.lower t w)).hom ≫
(has_SEMF.SEMF (h ≫ t.p)).i

lemma SEMF.nat_hom_comm_left : s.p ≫ (SEMF.nat_hom s t w) = h ≫ t.p :=
begin
  erw ←category.assoc,
  erw ←category.assoc,
  erw SEMF.unique_fac_left _ (SEMF.upper s w) (SEMF.lower t w),
  erw SEMF.fac,
end

lemma SEMF.nat_hom_comm_right : (SEMF.nat_hom s t w) ≫ t.i = s.i ≫ i :=
begin
  erw category.assoc,
  erw category.assoc,
  erw SEMF.unique_fac_right _ (SEMF.upper s w) (SEMF.lower t w),
  erw SEMF.fac,
end

end

namespace diagram
variable [has_SEMFs.{v} C]
variables {P Q R X Y Z : C}
variables {f : P ⟶ Q} {g : Q ⟶ R} {f' : X ⟶ Y} {g' : Y ⟶ Z} {α : P ⟶ X} {γ : R ⟶ Z}
variables (h : f ≫ g ≫ γ = α ≫ f' ≫ g')
variables [strong_epi f] [strong_epi f'] [mono g] [mono g']

def upper : SEMF (f ≫ g) :=
{ I := _,
  p := f,
  i := g,
  fac := rfl,
  i_mono := by apply_instance,
  p_strong_epi := by apply_instance }

def lower : SEMF (f' ≫ g') :=
{ I := _,
  p := f',
  i := g',
  fac := rfl,
  i_mono := by apply_instance,
  p_strong_epi := by apply_instance }

include h

def β : Q ⟶ Y :=
SEMF.nat_hom upper lower (show (f ≫ g) ≫ γ = α ≫ f' ≫ g', by rw [category.assoc, h])

def comm_left : f ≫ (β h) = α ≫ f' :=
SEMF.nat_hom_comm_left upper lower _

def comm_right : g ≫ γ = (β h) ≫ g' :=
(SEMF.nat_hom_comm_right upper lower _).symm

end diagram

end category_theory.epi_mono
