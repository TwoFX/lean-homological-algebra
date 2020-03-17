import category_theory.category
import algebra.group.hom
import data.opposite
import category_theory.opposites
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.kernels

universes v u

open category_theory.limits
open opposite
open add_monoid_hom

namespace category_theory

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

class preadditive :=
(hom_group : Π P Q : C, add_comm_group (P ⟶ Q))
(distrib_left' : Π P Q R : C, ∀ (f f' : P ⟶ Q) (g : Q ⟶ R),
  (f + f') ≫ g = f ≫ g + f' ≫ g . obviously)
(distrib_right' : Π P Q R : C, ∀ (f : P ⟶ Q) (g g' : Q ⟶ R),
  f ≫ (g + g') = f ≫ g + f ≫ g' . obviously)

attribute [instance] preadditive.hom_group
restate_axiom preadditive.distrib_left'
restate_axiom preadditive.distrib_right'
attribute [simp] preadditive.distrib_left
attribute [simp] preadditive.distrib_right

end category_theory

open category_theory

namespace category_theory.preadditive

section preadditive
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables [preadditive.{v} C]

def hom_right {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
mk' (λ g, f ≫ g) $ preadditive.distrib_right _ _ _ _ _

def hom_left (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
mk' (λ f, f ≫ g) $ λ f f', preadditive.distrib_left _ _ _ _ _ _ _

@[simp] lemma sub_distrib_left {P Q R : C} (f f' : P ⟶ Q) (g : Q ⟶ R) : (f - f') ≫ g = f ≫ g - f' ≫ g :=
map_sub (hom_left _ _) _ _

@[simp] lemma sub_distrib_right {P Q R : C} (f : P ⟶ Q) (g g' : Q ⟶ R) : f ≫ (g - g') = f ≫ g - f ≫ g' :=
map_sub (hom_right _ _) _ _

@[simp] lemma neg_left {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : (-f) ≫ g = -(f ≫ g) :=
map_neg (hom_left _ _) _

@[simp] lemma neg_right {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : f ≫ (-g) = -(f ≫ g) :=
map_neg (hom_right _ _) _

instance {P Q : C} {f : P ⟶ Q} [epi f] : epi (-f) :=
⟨λ R g g', by rw [neg_left, neg_left, ←neg_right, ←neg_right, cancel_epi]; exact neg_inj⟩

instance {P Q : C} {f : P ⟶ Q} [mono f] : mono (-f) :=
⟨λ R g g', by rw [neg_right, neg_right, ←neg_left, ←neg_left, cancel_mono]; exact neg_inj⟩ 

instance preadditive_has_zero_morphisms : has_zero_morphisms.{v} C :=
{ has_zero := infer_instance,
  comp_zero' := λ P Q f R, map_zero $ hom_right R f,
  zero_comp' := λ P Q R f, map_zero $ hom_left P f }

lemma cancel_zero_iff_mono {Q R : C} {f : Q ⟶ R} : mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
iff.intro (λ m P g, @zero_of_comp_mono _ _ _ _ _ _ _ _ m) $ λ h,
⟨λ P g g' hg, sub_eq_zero.1 $ h P _ $ eq.trans (map_sub (hom_left P f) g g') (sub_eq_zero.2 hg)⟩

lemma cancel_zero_iff_epi {P Q : C} {f : P ⟶ Q} : epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
iff.intro (λ e R g, @zero_of_comp_epi _ _ _ _ _ _ _ _ e) $ λ h,
⟨λ R g g' hg, sub_eq_zero.1 $ h R _ $ eq.trans (map_sub (hom_right R f) g g') (sub_eq_zero.2 hg)⟩

end preadditive

section equalizers
variables {C : Type u} [𝒞 : category.{v} C] [preadditive.{v} C]
include 𝒞

section
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
def has_limit_parallel_pair [has_limit (parallel_pair (f - g) 0)] :
  has_limit (parallel_pair f g) :=
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

end

section

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
def has_equalizers_of_has_kernels [has_kernels.{v} C] : has_equalizers.{v} C :=
@has_equalizers_of_has_limit_parallel_pair _ _
  (λ _ _ f g, has_limit_parallel_pair f g)

end

section
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
def has_colimit_parallel_pair [has_colimit (parallel_pair (f - g) 0)] :
  has_colimit (parallel_pair f g) :=
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

end

section

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
def has_coequalizers_of_has_cokernels [has_cokernels.{v} C] : has_coequalizers.{v} C :=
@has_coequalizers_of_has_colimit_parallel_pair _ _
  (λ _ _ f g, has_colimit_parallel_pair f g)

end

end equalizers

section opposite
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables [preadditive.{v} C]

-- Todo
-- Maybe we can use some properties of the opposite functor to make this less painful

end opposite

end category_theory.preadditive