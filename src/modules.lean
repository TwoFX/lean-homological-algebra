/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import algebra.category.Module.basic
import linear_algebra.basic
import abelian
import mod_bot
import mod_mono_epi
import mod_to_mathlib

open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.preadditive
open category_theory.limits.walking_parallel_pair

noncomputable theory

universe u

variables {R : Type u} [ring R]

namespace Module

section cokernel
variables {M N : Module R} (f : M ⟶ N)

local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

set_option trace.app_builder true

def cokernel_cocone : cofork f 0 :=
cokernel_cofork.of_π (up f.range.mkq) $ comp_mkq _

def cokernel_is_colimit : is_colimit (cokernel_cocone f) :=
cofork.is_colimit.mk _
  (λ s, f.range.liftq (cofork.π s) $ range_le_ker_iff.2 $ cokernel_cofork.condition s)
  (λ s, f.range.liftq_mkq (cofork.π s) $ range_le_ker_iff.2 $ cokernel_cofork.condition s)
  (λ s m h,
  begin
    ext,
    cases linear_map.range_eq_top.1 (submodule.range_mkq f.range) x with n hn,
    rw ←hn,
    conv_rhs { erw [←linear_map.comp_apply, submodule.liftq_mkq] },
    rw ←linear_map.comp_apply,
    apply linear_map.congr,
    exact h walking_parallel_pair.one,
  end)

end cokernel

section cokernel
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

instance module_has_cokernels : has_cokernels.{u} (Module R) :=
⟨λ _ _ f, ⟨cokernel_cocone f, cokernel_is_colimit f⟩⟩

end cokernel

section products

def module_has_limit_pair (M N : Module R) : has_limit (pair M N) :=
{ cone := @binary_fan.mk _ _ M N (of R $ M × N) (linear_map.fst R M N) (linear_map.snd R M N),
  is_limit :=
  { lift := λ s, linear_map.pair (s.π.app walking_pair.left) (s.π.app walking_pair.right),
    fac' := λ s j,
    begin
      ext,
      rw coe_comp,
      rw function.comp_apply,
      rw ←linear_map.comp_apply,
      cases j,
      { erw linear_map.fst_pair, },
      { erw linear_map.snd_pair, },
    end,
    uniq' := λ s m h,
    begin
      ext,
      { simp only [linear_map.pair_apply],
        rw ←h walking_pair.left,
        refl, },
      { simp only [linear_map.pair_apply],
        rw ←h walking_pair.right,
        refl, },
    end } }

section

local attribute [instance] module_has_limit_pair

instance module_has_binary_products : has_binary_products.{u} (Module R) :=
has_binary_products_of_has_limit_pair (Module R)

end

def module_has_colimit_pair (M N : Module R) : has_colimit (pair M N) :=
{ cocone := @binary_cofan.mk _ _ M N (of R $ M × N) (linear_map.inl R M N) (linear_map.inr R M N),
  is_colimit :=
  { desc := λ s, linear_map.copair (s.ι.app walking_pair.left) (s.ι.app walking_pair.right),
    fac' := λ s j,
    begin
      ext,
      rw coe_comp,
      rw function.comp_apply,
      rw ←linear_map.comp_apply,
      cases j,
      { erw linear_map.copair_inl, },
      { erw linear_map.copair_inr, },
    end,
    uniq' := λ s m h,
    begin
      ext,
      erw linear_map.copair_apply,
      erw ←h walking_pair.left,
      erw ←h walking_pair.right,
      simp only [function.comp_app, coe_comp],
      rw binary_cofan.mk_ι_app_left,
      rw binary_cofan.mk_ι_app_right,
      simp only [linear_map.inl_apply, linear_map.inr_apply],
      erw ←linear_map.map_add,
      conv_rhs { change m ((x.fst + 0, 0 + x.snd))},
      simp only [prod.mk.eta, add_zero, zero_add],
    end } }

section

local attribute [instance] module_has_colimit_pair

instance module_has_binary_coproducts : has_binary_coproducts.{u} (Module R) :=
has_binary_coproducts_of_has_colimit_pair (Module R)

end

end products

attribute [instance] has_zero_object.zero_morphisms_of_zero_object

section
variables {M N : Module R} (f : M ⟶ N)

lemma kernel_ker : kernel f = f.ker := rfl
lemma cokernel_quot : cokernel f = of R f.range.quotient := rfl

lemma kernel_ι_subtype : kernel.ι f = f.ker.subtype := rfl

end

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
        exact up_equiv' (equiv_range_of_ker_bot' f (ker_eq_bot_of_mono f)), },
      { haveI := m,
        exact equiv_range_of_ker_bot_fac' f (ker_eq_bot_of_mono f), }
    end },
  epi_is_cokernel := λ A B f e,
  { W := of R f.ker,
    g := f.ker.subtype,
    w := ker_comp f,
    is_colimit := begin
      refine cokernel.transport' _ _ _ _,
      { haveI := e,
        exact up_equiv' (equiv_range_of_range_top f (range_eq_top_of_epi f)), },
      { haveI := e,
        exact equiv_range_of_range_top_fac f (range_eq_top_of_epi f), },
    end } }

end Module
