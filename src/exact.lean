import category_theory.category
import abelian

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

structure exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :=
(h : f ≫ g = 0)
-- kernel.ι (cokernel.π f) is a kernel of g
(l : is_limit (fork.of_ι (kernel.ι (cokernel.π f)) (begin
  rw has_zero_morphisms.comp_zero,
  apply additive.cancel_zero_iff_epi.1 (abelian.to_im_epi f) _ _,
  rw ←category.assoc,
  rw abelian.f_factor f,
  exact h,
end) : fork g 0))

end

end category_theory.abelian