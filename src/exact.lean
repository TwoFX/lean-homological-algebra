import category_theory.category
import abelian

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

def exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : Prop :=
f ≫ g = 0 ∧ kernel.ι g ≫ cokernel.π f = 0

lemma exact_ker {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (e : exact f g) :
  is_limit (fork.of_ι (kernel.ι (cokernel.π f)) (begin
    rw has_zero_morphisms.comp_zero,
    have x : epi (abelian.factor_thru_image f) := by apply_instance,
    apply additive.cancel_zero_iff_epi.1 x _ (kernel.ι (cokernel.π f) ≫ g),
    rw ←category.assoc,
    rw abelian.image.fac f,
    exact e.1,
  end) : fork g 0) :=
{ lift := λ s, kernel.lift (cokernel.π f) (fork.ι s) (begin
  let t : s.X ⟶ kernel g := kernel.lift g (fork.ι s) (kernel_fork_condition _),
  have : t ≫ kernel.ι g = fork.ι s,
  { simp, },
  rw ←this,
  rw category.assoc,
  rw e.2,
  rw has_zero_morphisms.comp_zero,
end),
  fac' := λ s j, begin
    cases j,
    { simp, refl, },
    { simp, convert cone.w s walking_parallel_pair_hom.left, }
  end,
  uniq' := λ s m h, begin
    ext, erw h walking_parallel_pair.zero,
    erw limit.lift_π,
    refl,
  end }

end

end category_theory.abelian