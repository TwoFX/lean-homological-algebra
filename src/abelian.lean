import category_theory.category
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.kernels
import additive
import biproduct

open category_theory
open category_theory.additive
open category_theory.limits
open category_theory.additive

universes v u

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

/-- Is this really not in mathlib? -/
lemma epi_of_comp_epi {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} (e : epi (f ≫ g)) : epi g :=
⟨λ _ _ _ h, (cancel_epi (f ≫ g)).1 $ by simp only [h, category.assoc]⟩

lemma congr_comp {P Q R : C} {f g : P ⟶ Q} (e : f = g) (h : Q ⟶ R) : f ≫ h = g ≫ h :=
e ▸ eq.refl _

lemma congr_comp' {P Q R : C} {f g : Q ⟶ R} (e : f = g) (h : P ⟶ Q) : h ≫ f = h ≫ g :=
e ▸ eq.refl _

lemma mono_of_comp_mono {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} (m : mono (f ≫ g)) : mono f :=
⟨λ _ _ _ h, (cancel_mono (f ≫ g)).1 $ by simpa using congr_comp h g⟩

lemma kernel_fork_app_one [has_zero_morphisms.{v} C] {P Q : C} (f : P ⟶ Q) (s : fork f 0) :
  s.π.app walking_parallel_pair.one = 0 :=
begin
  rw ←cone_parallel_pair_right,
  erw has_zero_morphisms.comp_zero,
  refl,
end

end

namespace category_theory.abelian

section
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

class abelian extends preadditive.{v} C :=
(has_zero : has_zero_object.{v} C)
(finitely_complete : has_finite_limits.{v} C)
(finitely_cocomplete : has_finite_colimits.{v} C)
(epi_is_cokernel_of_kernel : Π {X Y : C} {f : X ⟶ Y} [epi f] (s : fork f 0) (h : is_limit s),
  is_colimit (cofork.of_π f (begin
    rw fork.condition, erw has_zero_morphisms.comp_zero, erw has_zero_morphisms.zero_comp,
  end) : cofork (fork.ι s) 0))
(mono_is_kernel_of_cokernel : Π {X Y : C} {f : X ⟶ Y} [mono f] (s : cofork f 0) (h : is_colimit s),
  is_limit (fork.of_ι f (begin
    rw cofork.condition, erw has_zero_morphisms.comp_zero, erw has_zero_morphisms.zero_comp,
  end) : fork (cofork.π s) 0))

attribute [instance] abelian.has_zero abelian.finitely_complete abelian.finitely_cocomplete

end

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞
variables  {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

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

set_option trace.check true

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

instance [epi f] : epi (biproduct.desc f g) :=
by { apply @epi_of_comp_epi _ _ _ _ _ biproduct.ι₁ _, simpa }



lemma epi_pullback [epi f] : epi (pullback.fst : pullback f g ⟶ X) :=
cancel_zero_iff_epi.2 $ λ R e h, begin
  sorry,
end

end
end category_theory.abelian