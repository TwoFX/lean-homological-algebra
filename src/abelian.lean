import category_theory.category
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.binary_products
import additive
import biproduct
import to_mathlib

open category_theory
open category_theory.additive
open category_theory.limits
open category_theory.additive

universes v u



namespace category_theory.abelian

section
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

class abelian extends preadditive.{v} C :=
(has_zero : has_zero_object.{v} C)
(has_binary_products : has_binary_products.{v} C)
(has_binary_coproducts : has_binary_coproducts.{v} C)
(has_kernels : has_kernels.{v} C)
(has_cokernels : has_cokernels.{v} C)
(epi_is_cokernel_of_kernel : Π {X Y : C} {f : X ⟶ Y} [epi f] (s : fork f 0) (h : is_limit s),
  is_colimit (cofork.of_π f (begin
    rw fork.condition, erw has_zero_morphisms.comp_zero, erw has_zero_morphisms.zero_comp,
  end) : cofork (fork.ι s) 0))
(mono_is_kernel_of_cokernel : Π {X Y : C} {f : X ⟶ Y} [mono f] (s : cofork f 0) (h : is_colimit s),
  is_limit (fork.of_ι f (begin
    rw cofork.condition, erw has_zero_morphisms.comp_zero, erw has_zero_morphisms.zero_comp,
  end) : fork (cofork.π s) 0))


attribute [instance] abelian.has_zero abelian.has_binary_products abelian.has_binary_coproducts abelian.has_kernels abelian.has_cokernels

end

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables  {X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z)

instance [mono a] [mono b] : has_limit (cospan a b) :=
begin
  let a_is_kernel_of_f := abelian.mono_is_kernel_of_cokernel (colimit.cocone (parallel_pair a 0)) (colimit.is_colimit _),
  let f := cokernel.π a,
  let b_is_kernel_of_g := abelian.mono_is_kernel_of_cokernel (colimit.cocone (parallel_pair b 0)) (colimit.is_colimit _),
  let g := cokernel.π b,
  let fg := prod.lift f g,
  let k := kernel.ι fg,
  have ffg : fg ≫ limits.prod.fst = f,
  { simp, },
  have gfg : fg ≫ limits.prod.snd = g,
  { simp, },
  have kf : k ≫ f = 0,
  { rw ←ffg, rw ←category.assoc, rw kernel.condition, rw has_zero_morphisms.zero_comp, },
  have kg : k ≫ g = 0,
  { rw ←gfg, rw ←category.assoc, rw kernel.condition, rw has_zero_morphisms.zero_comp, },
  let f_cone : fork f 0 := fork.of_ι k (begin rw kf, rw has_zero_morphisms.comp_zero, end),
  let g_cone : fork g 0 := fork.of_ι k (begin rw kg, rw has_zero_morphisms.comp_zero, end),
  let a' : kernel fg ⟶ X := a_is_kernel_of_f.lift f_cone,
  have aa' : k = a' ≫ a,
  { erw is_limit.fac _ f_cone walking_parallel_pair.zero, refl, },
  let b' : kernel fg ⟶ Y := b_is_kernel_of_g.lift g_cone,
  have bb' : k = b' ≫ b,
  { erw is_limit.fac _ g_cone walking_parallel_pair.zero, refl, },
  let limit_cone : pullback_cone a b := pullback_cone.mk a' b' (begin
    rw ←aa', rw bb',
  end),
  refine ⟨limit_cone, _⟩,
  refine ⟨λ s, kernel.lift fg (s.π.app walking_cospan.right ≫ b) _, _, _⟩,
  { apply limit.hom_ext, intro j, cases j,
    { simp only [category.assoc],
      rw limit.lift_π,
      rw ←category.assoc,
      erw ←pullback_cone.condition s,
      rw category.assoc,
      erw cokernel.condition,
      rw has_zero_morphisms.zero_comp,
      erw has_zero_morphisms.comp_zero, },
    { simp only [category.assoc],
      rw limit.lift_π,
      erw cokernel.condition,
      rw has_zero_morphisms.zero_comp,
      erw has_zero_morphisms.comp_zero, } },
    { apply_auto_param,
      cases j,
      { apply (cancel_mono a).1,
        sorry, },
      sorry,
      sorry,
      },
      sorry,

  --let a' : kernel fg ⟶ X := kernel.lift f k kf,
  --let b' : kernel fg ⟶ Y := kernel.lift g k kg,
  --{ erw ←limit.lift_π , }
end

end

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables  {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

instance : has_finite_limits.{v} C := sorry
instance : has_finite_colimits.{v} C := sorry

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
    ext, rw limit.lift_π, cases j,
    { unfold limit.π,
      erw ←blubb',
      conv_lhs { change m ≫ fork.ι (p_cone f g) ≫ biproduct.π₁ },
      rw ←category.assoc,
      erw h walking_parallel_pair.zero,
      refl, },
    { unfold limit.π,
      erw ←blubb',
      conv_lhs { change m ≫ fork.ι (p_cone f g) ≫ biproduct.π₂ },
      rw ←category.assoc,
      erw h walking_parallel_pair.zero,
      refl, },
    { unfold limit.π,
      erw ←blubb',
      conv_lhs { change m ≫ ((fork.ι (p_cone f g) ≫ biproduct.π₁) ≫ f) },
      simp only [category.assoc],
      rw ←category.assoc,
      erw h walking_parallel_pair.zero,
      rw ←category.assoc,
      refl, }
  end }

/- Now we need: biproduct.desc f g is a cokernel of pullback_to_biproduct -/

instance desc_of_f [epi f] : epi (biproduct.desc f (-g)) :=
by { apply @epi_of_comp_epi _ _ _ _ _ biproduct.ι₁ _, simpa }

/-- Aluffi IX.2.3, cf. Borceux 2, 1.7.6 -/
instance epi_pullback [epi f] : epi (pullback.snd : pullback f g ⟶ Y) :=
cancel_zero_iff_epi.2 $ λ R e h,
begin
  have := abelian.epi_is_cokernel_of_kernel _ (p_is_limit f g),
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
  have := abelian.epi_is_cokernel_of_kernel _ (p_is_limit f g),
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

section factor
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

variables {P Q : C} (f : P ⟶ Q)

def to_im : P ⟶ kernel (cokernel.π f) :=
kernel.lift (cokernel.π f) f $ cokernel.condition f

lemma f_factor : to_im f ≫ kernel.ι (cokernel.π f) = f :=
by erw limit.lift_π; refl

instance to_im_epi : epi (to_im f) :=
begin
  apply cancel_zero_iff_epi.2,
  intros R g h,
  let t := kernel.lift g (to_im f) h,
  have t_kernel : t ≫ kernel.ι g = to_im f := by simp,
  haveI : mono (kernel.ι g) := equalizer.ι_mono _ _,
  haveI : mono (kernel.ι (cokernel.π f)) := equalizer.ι_mono _ _,
  let u := kernel.ι g ≫ kernel.ι (cokernel.π f),
  haveI : mono u := by apply_instance,
  have u_is_kernel :=
    abelian.mono_is_kernel_of_cokernel (colimit.cocone (parallel_pair u 0)) (colimit.is_colimit _),
  let h := cokernel.π u, -- u is the kernel of h
  have fh : f ≫ h = 0,
  { conv_lhs { congr, rw ←f_factor f }, rw ←t_kernel,
    simp only [category.assoc],
    conv_lhs { congr, skip, rw ←category.assoc },
    change t ≫ u ≫ h = 0,
    rw cokernel.condition,
    rw has_zero_morphisms.comp_zero, },
  let l := cokernel.desc f h fh,
  have hl : cokernel.π f ≫ l = h := by simp; refl,
  have hg : kernel.ι (cokernel.π f) ≫ h = 0,
  { rw ←hl, rw ←category.assoc, rw kernel.condition, rw has_zero_morphisms.zero_comp, },
  let a_fork : fork h 0 := fork.of_ι (kernel.ι (cokernel.π f)) (begin
    rw hg, rw has_zero_morphisms.comp_zero,
  end),
  let s := is_limit.lift u_is_kernel a_fork,
  have su : s ≫ u = kernel.ι (cokernel.π f),
  { change (is_limit.lift u_is_kernel a_fork) ≫ u = kernel.ι (cokernel.π f),
    exact is_limit.fac u_is_kernel a_fork walking_parallel_pair.zero, },
  change s ≫ kernel.ι g ≫ kernel.ι (cokernel.π f) = kernel.ι (cokernel.π f) at su,
  conv_rhs at su { rw ←category.id_comp _ (kernel.ι (cokernel.π f))},
  rw ←category.assoc at su,
  have su' := (cancel_mono _).1 su,
  haveI : epi (kernel.ι g) := begin
    apply @epi_of_comp_epi _ _ _ _ _ s _,
    rw su',
    exact identity_is_epi _,
  end,
  have := kernel.condition g,
  exact cancel_zero_iff_epi.1 (by apply_instance) _ _ this,
end


end factor

end category_theory.abelian