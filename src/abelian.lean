import category_theory.category
import category_theory.limits.shapes.kernels
import additive
import to_mathlib

open category_theory
open category_theory.additive
open category_theory.limits

universes v u

namespace category_theory.abelian



variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
structure image_decomposition
  [has_zero_morphisms.{v} C] [has_finite_limits.{v} C] [has_finite_colimits.{v} C]
  {X Y : C} (f : X ⟶ Y) :=
(image_well_defined      : cokernel (kernel.ι f) ≅ kernel (cokernel.π f))
(composition_is_morphism : cokernel.π (kernel.ι f) ≫ image_well_defined.hom ≫ kernel.ι (cokernel.π f) = f)

end

section
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

class abelian extends preadditive.{v} C :=
(has_zero : has_zero_object.{v} C)
(finitely_complete : has_finite_limits.{v} C)
(finitely_cocomplete : has_finite_colimits.{v} C)
(has_image_decomposition : ∀ {P Q : C} (f : P ⟶ Q), image_decomposition.{v} f)

end

end category_theory.abelian