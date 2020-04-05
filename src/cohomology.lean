/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import abelian
import exact
import pseudoelements
import algebra.homology.homology
import epi_mono
import abelian_SEMF

open category_theory
open category_theory.limits
open category_theory.epi_mono
open cochain_complex

universes v u

namespace category_theory.abelian

open pseudoelements

section
variables {V : Type u} [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

local attribute [instance] has_zero_object.has_zero

def induced_map_on_boundaries {C C' : cochain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
  image (C.d i) ⟶ image (C'.d i) :=
SEMF.nat_hom (coimage_SEMF (C.d i)) (coimage_SEMF (C'.d i)) (cochain_complex.comm_at f i)

local attribute [instance] preadditive.has_equalizers_of_has_kernels

lemma induced_maps_commute {C C' : cochain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
image_to_kernel_map C i ≫ induced_map_on_cycles f (i+1) =
  induced_map_on_boundaries f i ≫ image_to_kernel_map C' i :=
begin
  apply (cancel_mono (kernel.ι (C'.d (i + 1)))).1,
  simp only [category.assoc],
  erw [limit.lift_π, limit.lift_π, SEMF.nat_hom_comm_right, ←category.assoc, limit.lift_π],
  refl,
end

def induced_map_on_cohomology {C C' : cochain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
  C.cohomology i ⟶ C'.cohomology i :=
cokernel.desc _ (induced_map_on_cycles f (i - 1 + 1) ≫ cokernel.π _)
begin
  rw [←category.assoc, induced_maps_commute, category.assoc, cokernel.condition],
  erw [has_zero_morphisms.comp_zero],
end

lemma induced_map_on_cycles_id {C : cochain_complex.{v} V} {i : ℤ} :
  induced_map_on_cycles (𝟙 C) i = 𝟙 _ :=
begin
  apply (cancel_mono (kernel.ι (C.d i))).1,
  erw [limit.lift_π, category.id_comp],
  erw fork.of_ι_app_zero,
  erw category.comp_id,
end

lemma induced_map_on_cycles_comp {C C' C'' : cochain_complex.{v} V} (f : C ⟶ C') (g : C' ⟶ C'')
  {i : ℤ} :
  induced_map_on_cycles (f ≫ g) i = induced_map_on_cycles f i ≫ induced_map_on_cycles g i :=
begin
  apply (cancel_mono (kernel.ι (C''.d i))).1,
  erw limit.lift_π,
  rw category.assoc,
  erw limit.lift_π,
  dsimp,
  conv_rhs { rw ←category.assoc },
  erw limit.lift_π,
  erw category.assoc,
end

def cohomology_functor : cochain_complex.{v} V ⥤ graded_object ℤ V :=
{ obj := λ C i, cohomology C i,
  map := λ C C' f i, induced_map_on_cohomology f i,
  map_id' := λ C, begin
    ext i,
    erw colimit.ι_desc,
    dsimp,
    erw category.comp_id,
    rw induced_map_on_cycles_id,
    erw category.id_comp,
  end,
  map_comp' := λ X Y Z f g, begin
    ext i,
    erw colimit.ι_desc,
    dsimp,
    rw ←category.assoc,
    erw colimit.ι_desc,
    dsimp,
    rw category.assoc,
    erw colimit.ι_desc,
    dsimp,
    rw induced_map_on_cycles_comp,
    rw category.assoc,
  end }

section
variable (V)

-- Not a good way to define it
structure SES_of_cochain_complexes :=
(A B C : cochain_complex.{v} V)
(f : A ⟶ B)
(g : B ⟶ C)
[monos : ∀ i, mono (differential_object.hom.f f i)]
[epis : ∀ i, epi (g.f i)]
(exacts : ∀ i, exact (f.f i) (g.f i))

end


end

end category_theory.abelian
