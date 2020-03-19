/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.constructions.pullbacks
import category_theory.limits.shapes.regular_mono
import category_theory.limits.shapes.images
import additive
import biproduct
import hom_to_mathlib

open category_theory
open category_theory.preadditive
open category_theory.limits

noncomputable theory

universes v u

namespace category_theory

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞



variables (C)

section prio
set_option default_priority 100

/-- A (preadditive) category `C` is called abelian if it has a zero object, all binary products and
    coproducts, all kernels and cokernels, and if every monomorphism is the kernel of some morphism
    and every epimorphism is the cokernel of somme morphism. -/
class abelian extends preadditive.{v} C :=
(has_zero_object : has_zero_object.{v} C)
(has_binary_products : has_binary_products.{v} C)
(has_binary_coproducts : has_binary_coproducts.{v} C)
(has_kernels : has_kernels.{v} C)
(has_cokernels : has_cokernels.{v} C)
(mono_is_kernel : Π {X Y : C} (f : X ⟶ Y) [mono f], normal_mono.{v} f)
(epi_is_cokernel : Π {X Y : C} (f : X ⟶ Y) [epi f], normal_epi.{v} f)

attribute [instance] abelian.has_zero_object abelian.has_binary_products abelian.has_binary_coproducts abelian.has_kernels abelian.has_cokernels
end prio
end category_theory

open category_theory

namespace category_theory.abelian
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

section factor

variables {P Q : C} (f : P ⟶ Q)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
def factor_thru_image : P ⟶ kernel (cokernel.π f) :=
kernel.lift (cokernel.π f) f $ cokernel.condition f

/-- `f` factors through its image via the canonical morphism `p`. -/
lemma image.fac : factor_thru_image f ≫ kernel.ι (cokernel.π f) = f :=
by erw limit.lift_π; refl

/-- The map `p : P ⟶ image f` is an epimorphism -/
instance : epi (factor_thru_image f) :=
let I := kernel (cokernel.π f), p := factor_thru_image f, i := kernel.ι (cokernel.π f) in
-- It will suffice to consider some g : I ⟶ R such that p ≫ g = 0 and show that g = 0.
(cancel_zero_iff_epi _).2 $ λ R (g : I ⟶ R) (hpg : p ≫ g = 0),
begin
  -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
  let u := kernel.ι g ≫ i,
  have hu := abelian.mono_is_kernel u,
  let h := hu.g,

  -- By hypothesis, p factors through the kernel of g via some t.
  obtain ⟨t, ht⟩ := kernel.lift' g p hpg,

  have fh : f ≫ h = 0, calc
    f ≫ h = (p ≫ i) ≫ h : (image.fac f).symm ▸ rfl
       ... = ((t ≫ kernel.ι g) ≫ i) ≫ h : ht ▸ rfl
       ... = t ≫ u ≫ h : by simp only [category.assoc]; conv_lhs { congr, skip, rw ←category.assoc }
       ... = t ≫ 0 : hu.w ▸ rfl
       ... = 0 : has_zero_morphisms.comp_zero _ _ _,

  -- h factors through the cokernel of f via some l.
  obtain ⟨l, hl⟩ := cokernel.desc' f h fh,

  have hih : i ≫ h = 0, calc
    i ≫ h = i ≫ cokernel.π f ≫ l : hl ▸ rfl
       ... = 0 ≫ l : by rw [←category.assoc, kernel.condition]
       ... = 0 : has_zero_morphisms.zero_comp _ _ _,

  -- i factors through u = ker h via some s.
  obtain ⟨s, hs⟩ := normal_mono.lift hu i hih,

  have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i, by rw [category.assoc, hs, category.id_comp],

  have : epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs'),

  -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
  exact (cancel_zero_iff_epi _).1 this _ _ (kernel.condition g)
end

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
def factor_thru_coimage : cokernel (kernel.ι f) ⟶ Q :=
cokernel.desc (kernel.ι f) f $ kernel.condition f

/-- `f` factors through its coimage via the canonical morphism `p`. -/
lemma coimage.fac : cokernel.π (kernel.ι f) ≫ factor_thru_coimage f = f :=
by erw colimit.ι_desc; refl

/-- The canonical morphism `i : coimage f ⟶ Q` is a monomorphism -/
instance : mono (factor_thru_coimage f) :=
let I := cokernel (kernel.ι f), i := factor_thru_coimage f, p := cokernel.π (kernel.ι f) in
(cancel_zero_iff_mono _).2 $ λ R (g : R ⟶ I) (hgi : g ≫ i = 0),
begin
  -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
  let u := p ≫ cokernel.π g,
  have hu := abelian.epi_is_cokernel u,
  let h := hu.g,

  -- By hypothesis, i factors through the cokernel of g via some t.
  obtain ⟨t, ht⟩ := cokernel.desc' g i hgi,

  have hf : h ≫ f = 0, calc
    h ≫ f = h ≫ (p ≫ i) : (coimage.fac f).symm ▸ rfl
    ... = h ≫ (p ≫ (cokernel.π g ≫ t)) : ht ▸ rfl
    ... = h ≫ u ≫ t : by simp only [category.assoc]; conv_lhs { congr, skip, rw ←category.assoc }
    ... = 0 ≫ t : by rw [←category.assoc, hu.w]
    ... = 0 : has_zero_morphisms.zero_comp _ _ _,

  -- h factors through the kernel of f via some l.
  obtain ⟨l, hl⟩ := kernel.lift' f h hf,

  have hhp : h ≫ p = 0, calc
    h ≫ p = (l ≫ kernel.ι f) ≫ p : hl ▸ rfl
    ... = l ≫ 0 : by rw [category.assoc, cokernel.condition]
    ... = 0 : has_zero_morphisms.comp_zero _ _ _,

  -- p factors through u = coker h via some s.
  obtain ⟨s, hs⟩ := normal_epi.desc hu p hhp,

  have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I, by rw [←category.assoc, hs, category.comp_id],

  have : mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs'),

  -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
  exact (cancel_zero_iff_mono _).1 this _ _ (cokernel.condition g)
end

end factor

section image

/-- An abelian category has all images. -/
instance : has_images.{v} C :=
{ has_image := λ X Y f, { F :=
  { I := cokernel (kernel.ι f),
    m := factor_thru_coimage f,
    m_mono := by apply_instance,
    e := cokernel.π (kernel.ι f),
    fac' := coimage.fac f },
  is_image :=
  { lift := λ F, cokernel.desc (kernel.ι f) F.e $
      (cancel_zero_iff_mono _).1 F.m_mono _ (limits.kernel.ι f ≫ F.e) $
        by rw [category.assoc, F.fac, kernel.condition],
    lift_fac' := λ F, (cancel_epi (cokernel.π (kernel.ι f))).1 $
      by erw [←category.assoc, colimit.ι_desc, coimage.fac, F.fac] } } }

end image

section mono_epi_iso
variables {X Y : C} (f : X ⟶ Y)

/-- In an abelian category, an monomorphism which is also an epimorphism is an isomorphism. -/
def mono_epi_iso [mono f] [epi f] : is_iso f :=
begin
  have hf := abelian.mono_is_kernel f,
  let s := kernel_fork.of_ι f hf.w,
  haveI : epi (s.π.app walking_parallel_pair.zero) :=
    show epi f, by apply_instance,
  exact epi_limit_cone_parallel_pair_is_iso _ _ s hf.is_limit
end

end mono_epi_iso

section cokernel_of_kernel
variables {X Y : C} {f : X ⟶ Y}

/-- If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π f (kernel_fork.condition s)) :=
begin
  haveI : epi (factor_thru_coimage f) := epi_of_epi_fac (coimage.fac f),
  haveI : is_iso (factor_thru_coimage f) := mono_epi_iso (factor_thru_coimage f),
  let i : cokernel (kernel.ι f) ≅ Y := as_iso (factor_thru_coimage f),
  let u : kernel f ≅ s.X :=
    functor.map_iso (cones.forget _) (is_limit.unique_up_to_iso (limit.is_limit _) h),
  have h : u.hom ≫ fork.ι s = kernel.ι f :=
    cone_morphism.w (is_limit.unique_up_to_iso (limit.is_limit _) h).hom walking_parallel_pair.zero,
  have x := cokernel.transport (kernel.ι f) (fork.ι s) u h,
  apply is_colimit.of_iso_colimit x,
  ext1,
  tactic.swap,
  exact i,
  cases j,
  { rw cokernel_cofork.app_zero,
    rw cokernel_cofork.app_zero,
    rw has_zero_morphisms.zero_comp,
    refl, },
  { exact coimage.fac f, }
end

end cokernel_of_kernel

section
local attribute [instance] preadditive.has_equalizers_of_has_kernels

/-- Any abelian category has pullbacks -/
@[priority 100]
instance : has_pullbacks.{v} C :=
has_pullbacks_of_has_binary_products_of_has_equalizers C

end

section
local attribute [instance] preadditive.has_coequalizers_of_has_cokernels

/-- Ant abelian category has pushouts -/
@[priority 100]
instance : has_pushouts.{v} C :=
has_pushouts_of_has_binary_coproducts_of_has_coequalizers C

end

namespace pullback_to_biproduct_is_kernel
variables  {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-! This section contains a slightly technical result about pullbacks and biproducts.
    We will need it in the proof that the pullback of an epimorphism is an epimorpism.
    TODO: This could in theory be placed in additive.lean -/

/-- The canonical map `pullback f g ⟶ biproduct X Y` -/
abbreviation pullback_to_biproduct : pullback f g ⟶ biproduct X Y :=
pullback.fst ≫ biproduct.ι₁ + pullback.snd ≫ biproduct.ι₂

lemma pullback_to_biproduct_π₁ : pullback_to_biproduct f g ≫ biproduct.π₁ = pullback.fst :=
by simp
lemma pullback_to_biproduct_π₂ : pullback_to_biproduct f g ≫ biproduct.π₂ = pullback.snd :=
by simp

/-- The canonical map `pullback f g ⟶ biproduct X Y` induces a kernel cone on the map
    `biproduct X Y ⟶ Z` induced by `f` and `g`. A slightly more intuitive way to think of
    this may be that it induces an equalizer fork on the maps induced by `(f, 0)` and
    `(0, g)`. -/
def pullback_to_biproduct_fork : fork (biproduct.desc f (-g)) 0 :=
kernel_fork.of_ι (pullback_to_biproduct f g) $
begin
  simp only [distrib_left, biproduct.ι₁_desc, neg_right, biproduct.ι₂_desc, category.assoc],
  exact sub_eq_zero.2 pullback.condition
end

/-- The canonical map `pullback f g ⟶ biproduct X Y` is a kernel of the map induced by
    `(f, -g)`. -/
def is_limit_pullback_to_biproduct : is_limit (pullback_to_biproduct_fork f g) :=
fork.is_limit.mk _
  (λ s, pullback.lift (fork.ι s ≫ biproduct.π₁) (fork.ι s ≫ biproduct.π₂) $
  sub_eq_zero.1 $ by erw [category.assoc, category.assoc, ←sub_distrib_right, sub_eq_add_neg,
    ←neg_right, fork.condition s, has_zero_morphisms.comp_zero]; refl)
  (λ s,
  begin
    ext; simp only [has_zero_morphisms.comp_zero, neg_right, sub_distrib_right, category.assoc],
    { erw [pullback_to_biproduct_π₁, limit.lift_π],
      refl },
    { erw [pullback_to_biproduct_π₂, limit.lift_π],
      refl }
  end)
  (λ s m h,
  begin
    apply pullback.hom_ext;
    erw limit.lift_π,
    { erw [pullback_cone.mk_π_app_left, ←pullback_to_biproduct_π₁, ←category.assoc,
        h walking_parallel_pair.zero],
      refl },
    { erw [pullback_cone.mk_π_app_right, ←pullback_to_biproduct_π₂, ←category.assoc,
        h walking_parallel_pair.zero],
      refl }
  end)

end pullback_to_biproduct_is_kernel

section epi_pullback
variables  {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- In an abelian category, the pullback of an epimorphism is an epimorphism.
    Aluffi IX.2.3, cf. Borceux 2, 1.7.6 -/
instance epi_pullback_of_epi_f [epi f] : epi (pullback.snd : pullback f g ⟶ Y) :=
-- It will suffice to consider some morphism e : Y ⟶ R such that
-- pullback.snd ≫ e = 0 and show that e = 0.
(cancel_zero_iff_epi _).2 $ λ R e h,
begin
  -- Consider the morphism u := (0, e) : biproduct X Y ⟶ R.
  let u := biproduct.desc (0 : X ⟶ R) e,
  -- The composite pullback f g ⟶ biproduct X Y ⟶ R is zero by assumption.
  have hu : pullback_to_biproduct_is_kernel.pullback_to_biproduct f g ≫ u = 0 := by simpa,

  -- pullback_to_biproduct f g is a kernel of (f, -g), so (f, -g) is a
  -- cokernel of pullback_to_biproduct f g
  have := epi_is_cokernel_of_kernel _
    (pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct f g),

  -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
  obtain ⟨d, hd⟩ := colimit_cokernel_cofork.desc' _ this u hu,
  change Z ⟶ R at d,
  change biproduct.desc f (-g) ≫ d = u at hd,

  -- But then f ≫ d = 0:
  have : f ≫ d = 0, calc
    f ≫ d = (biproduct.ι₁ ≫ biproduct.desc f (-g)) ≫ d : by rw biproduct.ι₁_desc
    ... = biproduct.ι₁ ≫ u : by erw [category.assoc, hd]
    ... = 0 : biproduct.ι₁_desc,

  -- But f is an epimorphism, so d = 0...
  have : d = 0 := (cancel_epi f).1 (by simpa),

  -- ...or, in other words, e = 0.
  calc
    e = biproduct.ι₂ ≫ u : by rw biproduct.ι₂_desc
    ... = biproduct.ι₂ ≫ biproduct.desc f (-g) ≫ d : by rw ←hd
    ... = biproduct.ι₂ ≫ biproduct.desc f (-g) ≫ 0 : by rw this
    ... = (biproduct.ι₂ ≫ biproduct.desc f (-g)) ≫ 0 : by rw ←category.assoc
    ... = 0 : has_zero_morphisms.comp_zero _ _ _
end

/-- In an abelian category, the pullback of an epimorphism is an epimorphism. -/
instance epi_pullback_of_epi_g [epi g] : epi (pullback.fst : pullback f g ⟶ X) :=
-- It will suffice to consider some morphism e : X ⟶ R such that
-- pullback.fst ≫ e = 0 and show that e = 0.
(cancel_zero_iff_epi _).2 $ λ R e h,
begin
  -- Consider the morphism u := (e, 0) : biproduct X Y ⟶ R.
  let u := biproduct.desc e (0 : Y ⟶ R),
  -- The composite pullback f g ⟶ biproduct X Y ⟶ R is zero by assumption.
  have hu : pullback_to_biproduct_is_kernel.pullback_to_biproduct f g ≫ u = 0 := by simpa,

  -- pullback_to_biproduct f g is a kernel of (f, -g), so (f, -g) is a
  -- cokernel of pullback_to_biproduct f g
  have := epi_is_cokernel_of_kernel _
    (pullback_to_biproduct_is_kernel.is_limit_pullback_to_biproduct f g),

  -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
  obtain ⟨d, hd⟩ := colimit_cokernel_cofork.desc' _ this u hu,
  change Z ⟶ R at d,
  change biproduct.desc f (-g) ≫ d = u at hd,

  -- But then (-g) ≫ d = 0:
  have : (-g) ≫ d = 0, calc
    (-g) ≫ d = (biproduct.ι₂ ≫ biproduct.desc f (-g)) ≫ d : by rw biproduct.ι₂_desc
    ... = biproduct.ι₂ ≫ u : by erw [category.assoc, hd]
    ... = 0 : biproduct.ι₂_desc,

  -- But g is an epimorphism, thus so is -g, so d = 0...
  have : d = 0 := (cancel_epi (-g)).1 (by simpa),

  -- ...or, in other words, e = 0.
  calc
    e = biproduct.ι₁ ≫ u : by rw biproduct.ι₁_desc
    ... = biproduct.ι₁ ≫ biproduct.desc f (-g) ≫ d : by rw ←hd
    ... = biproduct.ι₁ ≫ biproduct.desc f (-g) ≫ 0 : by rw this
    ... = (biproduct.ι₁ ≫ biproduct.desc f (-g)) ≫ 0 : by rw ←category.assoc
    ... = 0 : has_zero_morphisms.comp_zero _ _ _
end

end epi_pullback

end category_theory.abelian
