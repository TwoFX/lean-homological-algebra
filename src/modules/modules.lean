/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import algebra.category.Module.basic
import linear_algebra.basic
import abelian
import exact
import modules.trivial_equivalence
import modules.mono_epi
import modules.to_mathlib

open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.preadditive
open category_theory.limits.walking_parallel_pair
open linear_map

noncomputable theory

universe u

variables {R : Type u} [ring R]

namespace Module

section cokernel
variables {M N : Module R} (f : M ⟶ N)

def cokernel_cocone : cofork f 0 :=
cokernel_cofork.of_π (up f.range.mkq) $ comp_mkq _

def cokernel_is_colimit : is_colimit (cokernel_cocone f) :=
cofork.is_colimit.mk _
  (λ s, f.range.liftq (cofork.π s) $ range_le_ker_iff.2 $ cokernel_cofork.condition s)
  (λ s, f.range.liftq_mkq (cofork.π s) _)
  (λ s m h,
  begin
    ext,
    cases range_eq_top.1 (submodule.range_mkq f.range) x with n hn,
    rw ←hn,
    conv_rhs { erw [←comp_apply, submodule.liftq_mkq] },
    rw ←comp_apply,
    apply linear_map.congr,
    exact h walking_parallel_pair.one,
  end)

end cokernel

section cokernel

instance module_has_cokernels : has_cokernels.{u} (Module R) :=
⟨λ _ _ f, ⟨cokernel_cocone f, cokernel_is_colimit f⟩⟩

end cokernel

section products

def module_has_limit_pair (M N : Module R) : has_limit (pair M N) :=
{ cone := @binary_fan.mk _ _ M N (of R $ M × N) (fst R M N) (snd R M N),
  is_limit :=
  { lift := λ s, prod (s.π.app walking_pair.left) (s.π.app walking_pair.right),
    fac' := λ s j, walking_pair.cases_on j (fst_prod _ _) (snd_prod _ _),
    uniq' := λ s m h,
    begin
      ext,
      rw prod_apply,
      { rw ←h walking_pair.left, refl },
      { rw ←h walking_pair.right, refl }
    end } }

section

local attribute [instance] module_has_limit_pair

instance module_has_binary_products : has_binary_products.{u} (Module R) :=
has_binary_products_of_has_limit_pair (Module R)

end

def module_has_colimit_pair (M N : Module R) : has_colimit (pair M N) :=
{ cocone := @binary_cofan.mk _ _ M N (of R $ M × N) (inl R M N) (inr R M N),
  is_colimit :=
  { desc := λ s, coprod (s.ι.app walking_pair.left) (s.ι.app walking_pair.right),
    fac' := λ s j, walking_pair.cases_on j (coprod_inl _ _) (coprod_inr _ _),
    uniq' := λ s m h,
    begin
      ext,
      erw [coprod_apply, ←h walking_pair.left, ←h walking_pair.right,
        binary_cofan.mk_ι_app_left, binary_cofan.mk_ι_app_right, comp_apply, comp_apply, ←map_add],
      apply congr_arg,
      rw [inl_apply, inr_apply, prod.mk_add_mk, zero_add, add_zero, prod.mk.eta]
    end } }

section

local attribute [instance] module_has_colimit_pair

instance module_has_binary_coproducts : has_binary_coproducts.{u} (Module R) :=
has_binary_coproducts_of_has_colimit_pair (Module R)

end

end products

instance : abelian.{u} (Module.{u} R) :=
{ hom_group := by apply_instance,
  distrib_left' := λ P Q R f f' g,
    show (f + f') ≫ g = f ≫ g + f' ≫ g, by ext; simp,
  distrib_right' := λ P Q R f g g',
    show f ≫ (g + g') = f ≫ g + f ≫ g', by ext; simp,
  has_zero_object := by apply_instance,
  has_binary_products := by apply_instance,
  has_binary_coproducts := by apply_instance,
  has_kernels := by apply_instance,
  has_cokernels := by apply_instance,
  mono_is_kernel := λ A B f m,
  { Z := of R f.range.quotient,
    g := f.range.mkq,
    w := comp_mkq f,
    is_limit := begin
      refine kernel.transport _ _ _ _,
      { haveI := m,
        exact up_equiv (equiv_range_of_ker_bot f (ker_eq_bot_of_mono f)), },
      { ext, refl }
    end },
  epi_is_cokernel := λ A B f e,
  { W := of R f.ker,
    g := f.ker.subtype,
    w := ker_comp f,
    is_colimit := begin
      refine cokernel.transport _ _ _ _,
      { haveI := e,
        exact up_equiv (equiv_range_of_range_top f (range_eq_top_of_epi f)), },
      { ext, refl }
    end } }

section
variables {X Y Z : Module R} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma exact_is_exact : exact f g ↔ f.range = g.ker :=
⟨λ h, le_antisymm (range_le_ker_iff.2 h.1) (ker_le_range_iff.2 h.2),
 λ h, ⟨range_le_ker_iff.1 $ le_of_eq h, ker_le_range_iff.1 $ le_of_eq h.symm⟩⟩

 end

end Module
