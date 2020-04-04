/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.category
import abelian
import epi_mono

open category_theory
open category_theory.epi_mono
open category_theory.lifting
open category_theory.limits

universes v u

namespace category_theory.abelian
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables {X Y : C} (f : X ⟶ Y)

def strong_epi_of_epi [epi f] : strong_epi f :=
begin
  haveI : normal_epi f := abelian.epi_is_cokernel f,
  apply_instance,
end

def image_SEMF : SEMF f :=
{ I := _,
  p := factor_thru_image f,
  i := kernel.ι (cokernel.π f),
  fac := image.fac f,
  i_mono := by apply_instance,
  p_strong_epi := strong_epi_of_epi _ }

def coimage_SEMF : SEMF f :=
{ I := _,
  p := cokernel.π (kernel.ι f),
  i := factor_thru_coimage f,
  fac := coimage.fac f,
  i_mono := by apply_instance,
  p_strong_epi := strong_epi_of_epi _ }

def image_well_defined : cokernel (kernel.ι f) ≅ kernel (cokernel.π f) :=
SEMF.unique _ (coimage_SEMF f) (image_SEMF f)

lemma full_image_fac :
  cokernel.π (kernel.ι f) ≫ (image_well_defined f).hom ≫ kernel.ι (cokernel.π f) = f :=
begin
  erw SEMF.unique_fac_right,
  erw coimage.fac,
end

instance : has_SEMFs.{v} C :=
{ has_SEMF := λ X Y f,
  { SEMF := image_SEMF f } }

end category_theory.abelian
