import category_theory.category
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.constructions.limits_of_products_and_equalizers
import finite_products
import additive
import biproduct
import hom_to_mathlib

open category_theory
open category_theory.additive
open category_theory.limits
open category_theory.additive

noncomputable theory

universes v u

namespace category_theory.abelian

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables [has_zero_morphisms.{v} C] {X Y : C}

/-- `is_kernel f` means that `f` is the kernel of some morphism `of`. -/
structure is_kernel (f : X ⟶ Y) :=
(Z : C)
(of : Y ⟶ Z)
(condition : f ≫ of = 0)
(l : is_limit $ kernel_fork.of_ι of f condition)

/-- Any map that is zero when composed with `s.of` factors through `f`. -/
def is_kernel.lift {f : X ⟶ Y} (s : is_kernel f) {W : C} (g : W ⟶ Y) (h : g ≫ s.of = 0) :
  { l : W ⟶ X // l ≫ f = g } :=
⟨is_limit.lift s.l $ kernel_fork.of_ι s.of g h, is_limit.fac s.l _ walking_parallel_pair.zero⟩

/-- `is_cokernel f` means that `f` is the cokernel of some morphism `of`. -/
structure is_cokernel (f : X ⟶ Y) :=
(Z : C)
(of : Z ⟶ X)
(condition : of ≫ f = 0)
(l : is_colimit $ cokernel_cofork.of_π of f condition)

/-- Any map that is zero when precomposed with `s.of` factors through `f`. -/
def is_cokernel.desc {f : X ⟶ Y} (s : is_cokernel f) {W : C} (g : X ⟶ W) (h : s.of ≫ g = 0) :
  { l : Y ⟶ W // f ≫ l = g } :=
⟨is_colimit.desc s.l $ cokernel_cofork.of_π s.of g h, is_colimit.fac s.l _ walking_parallel_pair.one⟩

end

section
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A (preadditive) category `C` is called abelian if it has a zero object, all binary products and
    coproducts, all kernels and cokernels, and if every monomorphism is the kernel of some morphism
    and every epimorphism is the cokernel of somme morphism. -/
class abelian extends preadditive.{v} C :=
(has_zero : has_zero_object.{v} C)
(has_binary_products : has_binary_products.{v} C)
(has_binary_coproducts : has_binary_coproducts.{v} C)
(has_kernels : has_kernels.{v} C)
(has_cokernels : has_cokernels.{v} C)
(mono_is_kernel : Π {X Y : C} (f : X ⟶ Y) [mono f], is_kernel.{v} f)
(epi_is_cokernel : Π {X Y : C} (f : X ⟶ Y) [epi f], is_cokernel.{v} f)

attribute [instance] abelian.has_zero abelian.has_binary_products abelian.has_binary_coproducts abelian.has_kernels abelian.has_cokernels

end

section factor
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

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
cancel_zero_iff_epi.2 $ λ R (g : I ⟶ R) (hpg : p ≫ g = 0),
begin
  -- Since C is abelian, u := ker g ≫ i is the kernel of some morphism h.
  let u := kernel.ι g ≫ i,
  have hu := abelian.mono_is_kernel u,
  let h := hu.of,

  -- By hypothesis, p factors through the kernel of g via some t.
  obtain ⟨t, ht⟩ := kernel.lift' g p hpg,

  have fh : f ≫ h = 0, calc
    f ≫ h = (p ≫ i) ≫ h : (image.fac f).symm ▸ rfl
       ... = ((t ≫ kernel.ι g) ≫ i) ≫ h : ht ▸ rfl
       ... = t ≫ u ≫ h : by simp only [category.assoc]; conv_lhs { congr, skip, rw ←category.assoc }
       ... = t ≫ 0 : hu.condition ▸ rfl
       ... = 0 : has_zero_morphisms.comp_zero _ _ _,

  -- h factors through the cokernel of f via some l.
  obtain ⟨l, hl⟩ := cokernel.desc' f h fh,

  have hih : i ≫ h = 0, calc
    i ≫ h = i ≫ cokernel.π f ≫ l : hl ▸ rfl
       ... = 0 ≫ l : by rw [←category.assoc, kernel.condition]
       ... = 0 : has_zero_morphisms.zero_comp _ _ _,

  -- i factors through u = ker h via some s.
  obtain ⟨s, hs⟩ := is_kernel.lift hu i hih,

  have hs' : (s ≫ kernel.ι g) ≫ i = 𝟙 I ≫ i, by rw [category.assoc, hs, category.id_comp],

  have : epi (kernel.ι g) := epi_of_epi_fac ((cancel_mono _).1 hs'),

  -- ker g is an epimorphism, but ker g ≫ g = 0 = ker g ≫ 0, so g = 0 as required.
  exact cancel_zero_iff_epi.1 this _ _ (kernel.condition g)
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
cancel_zero_iff_mono.2 $ λ R (g : R ⟶ I) (hgi : g ≫ i = 0),
begin
  -- Since C is abelian, u := p ≫ coker g is the cokernel of some morphism h.
  let u := p ≫ cokernel.π g,
  have hu := abelian.epi_is_cokernel u,
  let h := hu.of,

  -- By hypothesis, i factors through the cokernel of g via some t.
  obtain ⟨t, ht⟩ := cokernel.desc' g i hgi,

  have hf : h ≫ f = 0, calc
    h ≫ f = h ≫ (p ≫ i) : (coimage.fac f).symm ▸ rfl
    ... = h ≫ (p ≫ (cokernel.π g ≫ t)) : ht ▸ rfl
    ... = h ≫ u ≫ t : by simp only [category.assoc]; conv_lhs { congr, skip, rw ←category.assoc }
    ... = 0 ≫ t : by rw [←category.assoc, hu.condition]
    ... = 0 : has_zero_morphisms.zero_comp _ _ _,

  -- h factors through the kernel of f via some l.
  obtain ⟨l, hl⟩ := kernel.lift' f h hf,

  have hhp : h ≫ p = 0, calc
    h ≫ p = (l ≫ kernel.ι f) ≫ p : hl ▸ rfl
    ... = l ≫ 0 : by rw [category.assoc, cokernel.condition]
    ... = 0 : has_zero_morphisms.comp_zero _ _ _,

  -- p factors through u = coker h via some s.
  obtain ⟨s, hs⟩ := is_cokernel.desc hu p hhp,

  have hs' : p ≫ cokernel.π g ≫ s = p ≫ 𝟙 I, by rw [←category.assoc, hs, category.comp_id],

  have : mono (cokernel.π g) := mono_of_mono_fac ((cancel_epi _).1 hs'),

  -- coker g is a monomorphism, but g ≫ coker g = 0 = 0 ≫ coker g, so g = 0 as required.
  exact cancel_zero_iff_mono.1 this _ _ (cokernel.condition g)
end

end factor

section mono_epi_iso
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables {X Y : C} (f : X ⟶ Y)

/-- In an abelian category, an monomorphism which is also an epimorphism is an isomorphism. -/
def mono_epi_iso [mono f] [epi f] : is_iso f :=
begin
  have hf := abelian.mono_is_kernel f,
  let s := kernel_fork.of_ι hf.of f hf.condition,
  haveI : epi (s.π.app walking_parallel_pair.zero) :=
    show epi f, by apply_instance,
  exact epi_limit_cone_parallel_pair_is_iso _ _ s hf.l
end

end mono_epi_iso

section cokernel_of_kernel
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables {X Y : C} {f : X ⟶ Y}

/-(epi_is_cokernel_of_kernel : Π {X Y : C} {f : X ⟶ Y} [epi f] (s : fork f 0) (h : is_limit s),
  is_colimit (cofork.of_π f (begin
    rw fork.condition, erw has_zero_morphisms.comp_zero, erw has_zero_morphisms.zero_comp,
  end) : cofork (fork.ι s) 0))-/
/-(mono_is_kernel_of_cokernel : Π {X Y : C} {f : X ⟶ Y} [mono f] (s : cofork f 0) (h : is_colimit s),
  is_limit (fork.of_ι f (begin
    rw cofork.condition, erw has_zero_morphisms.comp_zero, erw has_zero_morphisms.zero_comp,
  end) : fork (cofork.π s) 0))-/

/-- If `f` is an epimorphism and `s` is some limit kernel cone on `f`, then `f` is a cokernel
    of `fork.ι s`. -/
def epi_is_cokernel_of_kernel [epi f] (s : fork f 0) (h : is_limit s) :
  is_colimit (cokernel_cofork.of_π (fork.ι s) f (kernel_fork_condition s)) :=
begin
  haveI : epi (factor_thru_coimage f) := epi_of_epi_fac (coimage.fac f),
  haveI : is_iso (factor_thru_coimage f) := mono_epi_iso (factor_thru_coimage f),
  let i : cokernel (kernel.ι f) ≅ Y := as_iso (factor_thru_coimage f),
  let u : kernel f ≅ s.X :=
    functor.map_iso cones.forget (is_limit.unique_up_to_iso (limit.is_limit _) h),
  have h : u.hom ≫ fork.ι s = kernel.ι f :=
    cone_morphism.w (is_limit.unique_up_to_iso (limit.is_limit _) h).hom walking_parallel_pair.zero,
  have x := cokernel.transport (kernel.ι f) (fork.ι s) u h,
  apply is_colimit.of_iso_colimit x,
  ext,
  tactic.swap,
  exact i,
  cases j,
  { rw cokernel_cofork_app_zero,
    rw cokernel_cofork_app_zero,
    rw has_zero_morphisms.zero_comp,
    refl, },
  { exact coimage.fac f, }
end

end cokernel_of_kernel

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

def fg_has_limit : has_limit (parallel_pair f g) :=
{ cone := fork.of_ι (kernel.ι (f - g)) (sub_eq_zero.1 $
    by rw ←sub_distrib_right; exact kernel.condition _),
  is_limit :=
  { lift := λ s, kernel.lift (f - g) (fork.ι s) $
      by rw sub_distrib_right; apply sub_eq_zero.2; exact fork.condition _,
    fac' := λ s j, begin cases j, { simp, refl, },
      { simp, convert cone.w s walking_parallel_pair_hom.left, } end,
    uniq' := λ s m h, begin
      ext, convert h walking_parallel_pair.zero, simp, refl,
    end } }

def F_has_limit {F : walking_parallel_pair ⥤ C} : has_limit F :=
begin
  convert fg_has_limit (F.map walking_parallel_pair_hom.left) (F.map walking_parallel_pair_hom.right),
  apply category_theory.functor.ext,
  tidy,
  cases f,
  tidy,
end

instance : has_limits_of_shape.{v} walking_parallel_pair C :=
{ has_limit := λ F, F_has_limit }

instance : has_equalizers.{v} C :=
{ has_limits_of_shape := by apply_instance }

def fg_has_colimit : has_colimit (parallel_pair f g) :=
{ cocone := cofork.of_π (cokernel.π (f - g)) (sub_eq_zero.1 $
    by rw ←sub_distrib_left; exact cokernel.condition _),
  is_colimit :=
  { desc := λ s, cokernel.desc (f - g) (cofork.π s) $
      by rw sub_distrib_left; apply sub_eq_zero.2; exact cofork.condition _,
    fac' := λ s j, begin cases j,
      { simp, convert cocone.w s walking_parallel_pair_hom.left, },
      { simp, refl, } end,
    uniq' := λ s m h, begin
      ext, convert h walking_parallel_pair.one, simp, refl,
    end } }

def F_has_colimit {F : walking_parallel_pair ⥤ C} : has_colimit F :=
begin
  convert fg_has_colimit (F.map walking_parallel_pair_hom.left) (F.map walking_parallel_pair_hom.right),
  apply category_theory.functor.ext,
  tidy,
  cases f,
  tidy,
end

instance : has_colimits_of_shape.{v} walking_parallel_pair C :=
{has_colimit := λ F, F_has_colimit}

instance : has_coequalizers.{v} C :=
{ has_colimits_of_shape := by apply_instance }

end

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables  {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

local attribute [instance] has_zero_object.has_initial_of_has_zero_object
local attribute [instance] has_zero_object.has_terminal_of_has_zero_object

/-instance : has_finite_products.{v} C :=
{ has_limits_of_shape := λ J a b, begin resetI, exact trunc.out has_trunc_finite_products end }

instance : has_finite_limits.{v} C :=
finite_limits_from_equalizers_and_finite_products-/

instance : has_pullbacks.{v} C := sorry

def pullback_to_biproduct : pullback f g ⟶ biproduct X Y :=
pullback.fst ≫ biproduct.ι₁ + pullback.snd ≫ biproduct.ι₂

lemma v : pullback_to_biproduct f g ≫ biproduct.desc f (-g) = 0 :=
begin
  unfold pullback_to_biproduct,
  simp,
  apply sub_eq_zero.2,
  exact pullback.condition,
end

def p_cone : fork (biproduct.desc f (-g)) 0 :=
fork.of_ι (pullback_to_biproduct f g) $ by simp [v]

def pullback_cone_of_fork (s : fork (biproduct.desc f (-g)) 0) : pullback_cone f g :=
pullback_cone.mk (fork.ι s ≫ biproduct.π₁) (fork.ι s ≫ biproduct.π₂) $ begin
  simp only [category.assoc],
  apply sub_eq_zero.1,
  rw ←sub_distrib_right,
  rw sub_eq_add_neg,
  rw ←neg_right,
  erw fork.condition s,
  erw has_zero_morphisms.comp_zero,
end

lemma pullback_cone_of_fork_app_left (s : fork (biproduct.desc f (-g)) 0) :
  (pullback_cone_of_fork f g s).π.app walking_cospan.left = fork.ι s ≫ biproduct.π₁ := rfl

lemma pullback_cone_of_fork_app_right (s : fork (biproduct.desc f (-g)) 0) :
  (pullback_cone_of_fork f g s).π.app walking_cospan.right = fork.ι s ≫ biproduct.π₂ := rfl

section 

lemma blubb' (j : walking_cospan) : (pullback_cone_of_fork f g (p_cone f g)).π.app j =
  (limit.cone (cospan f g)).π.app j :=
begin
  cases j,
  { change ((pullback.fst ≫ biproduct.ι₁ + pullback.snd ≫ biproduct.ι₂) ≫ biproduct.π₁) =
      limit.π (cospan f g) walking_cospan.left,
    simp },
  { change ((pullback.fst ≫ biproduct.ι₁ + pullback.snd ≫ biproduct.ι₂) ≫ biproduct.π₂) =
      limit.π (cospan f g) walking_cospan.right,
    simp },
  change ((pullback.fst ≫ biproduct.ι₁ + pullback.snd ≫ biproduct.ι₂) ≫ biproduct.π₁) ≫ f =
      limit.π (cospan f g) walking_cospan.one,
  simp,
  convert limit.w (cospan f g) walking_cospan.hom.inl,
end

end


lemma test₁ (s : fork (biproduct.desc f (-g)) 0) :
  fork.ι s ≫ biproduct.π₁ = 
  (pullback_cone_of_fork f g s).π.app walking_cospan.left := rfl

lemma test₂ (s : fork (biproduct.desc f (-g)) 0) :
  fork.ι s ≫ biproduct.π₂ = (pullback_cone_of_fork f g s).π.app walking_cospan.right := rfl

/-- pullback_to_biproduct is a kernel of biproduct.desc f g -/
def p_is_limit : is_limit (p_cone f g) :=
{ lift := λ s, limit.lift (cospan f g) (pullback_cone_of_fork f g s),
  fac' := λ s j,
  begin
    cases j,
    { ext, 
      { simp only [category.assoc], erw test₁,
        erw blubb',
        erw limit.lift_π,
        refl, },
      { simp only [category.assoc], erw test₂,
        erw blubb',
        erw limit.lift_π,
        refl, } },
    { rw kernel_fork_app_one, rw kernel_fork_app_one, erw has_zero_morphisms.comp_zero, refl, }
  end,
  uniq' := λ s m h,
  begin
    -- TODO: Figure out why ext does not trigger this
    apply pullback.hom_ext; rw limit.lift_π,
    { conv_lhs { change m ≫ (limit.cone (cospan f g)).π.app walking_cospan.left },
      erw ←blubb',
      rw pullback_cone_of_fork_app_left,
      rw ←category.assoc,
      erw h walking_parallel_pair.zero,
      refl, },
    { conv_lhs { change m ≫ (limit.cone (cospan f g)).π.app walking_cospan.right },
      erw ←blubb',
      rw pullback_cone_of_fork_app_right,
      rw ←category.assoc,
      erw h walking_parallel_pair.zero,
      refl, },
  end }

/- Now we need: biproduct.desc f g is a cokernel of pullback_to_biproduct -/

instance desc_of_f [epi f] : epi (biproduct.desc f (-g)) :=
by { apply @epi_of_comp_epi _ _ _ _ _ biproduct.ι₁ _, simpa }

/-- Aluffi IX.2.3, cf. Borceux 2, 1.7.6 -/
instance epi_pullback [epi f] : epi (pullback.snd : pullback f g ⟶ Y) :=
cancel_zero_iff_epi.2 $ λ R e h,
begin
  have := epi_is_cokernel_of_kernel _ (p_is_limit f g),
  let u := biproduct.desc (0 : X ⟶ R) e,
  have pu : pullback_to_biproduct f g ≫ u = 0,
  { unfold pullback_to_biproduct, simp, exact h, },
  let pu_cocone : cofork (pullback_to_biproduct f g) 0 := cofork.of_π u (begin
    rw pu, rw has_zero_morphisms.zero_comp,
  end),
  let d : Z ⟶ R := is_colimit.desc this pu_cocone,
  have hf : f = biproduct.ι₁ ≫ biproduct.desc f (-g),
  { simp, },
  have b := is_colimit.fac this pu_cocone walking_parallel_pair.one,
  conv_rhs at b { change u },
  conv_lhs at b { congr, change biproduct.desc f (-g) },
  have hfd : f ≫ d = 0,
  { rw hf, rw category.assoc, erw b, simp, },
  have hd : d = 0 := cancel_zero_iff_epi.1 (by apply_instance) _ _ hfd,
  have hu : u = 0,
  { rw ←b, change biproduct.desc f (-g) ≫ d = 0, rw hd, simp, },
  have hh : biproduct.ι₂ ≫ u = 0,
  { rw hu, simp, },
  rw biproduct.ι₂_desc at hh,
  exact hh,
end

instance desc_of_g [epi g] : epi (biproduct.desc f (-g)) :=
by { apply @epi_of_comp_epi _ _ _ _ _ biproduct.ι₂ _, simp, apply_instance, }

instance epi_pullback' [epi g] : epi (pullback.fst : pullback f g ⟶ X) :=
cancel_zero_iff_epi.2 $ λ R e h,
begin
  have := epi_is_cokernel_of_kernel _ (p_is_limit f g),
  let u := biproduct.desc e (0 : Y ⟶ R),
  have pu : pullback_to_biproduct f g ≫ u = 0,
  { unfold pullback_to_biproduct, simp, exact h, },
  let pu_cocone : cofork (pullback_to_biproduct f g) 0 := cofork.of_π u (begin
    rw pu, rw has_zero_morphisms.zero_comp,
  end),
  let d : Z ⟶ R := is_colimit.desc this pu_cocone,
  have hg : -g = biproduct.ι₂ ≫ biproduct.desc f (-g),
  { simp, },
  have b := is_colimit.fac this pu_cocone walking_parallel_pair.one,
  conv_rhs at b { change u },
  conv_lhs at b { congr, change biproduct.desc f (-g) },
  have hgd : -g ≫ d = 0,
  { rw hg, rw category.assoc, erw b, simp, },
  have hd : d = 0 := cancel_zero_iff_epi.1 (by apply_instance) _ _ hgd,
  have hu : u = 0,
  { rw ←b, change biproduct.desc f (-g) ≫ d = 0, rw hd, simp, },
  have hh : biproduct.ι₁ ≫ u = 0,
  { rw hu, simp, },
  rw biproduct.ι₁_desc at hh,
  exact hh,
end

end



end category_theory.abelian
