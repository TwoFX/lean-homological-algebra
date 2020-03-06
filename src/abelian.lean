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

end

namespace category_theory.abelian

section
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

attribute [instance] abelian.has_zero abelian.finitely_complete abelian.finitely_cocomplete

end

section
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

lemma epi_pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [epi f] : epi (pullback.fst : pullback f g ⟶ X) :=
cancel_zero_iff_epi.2 $ λ R e h, begin
  have o_epi : epi (biproduct.out f g),
  { apply @epi_of_comp_epi _ _ _ _ _ (biproduct.biproduct.s₁ X Y) _, simpa },
  sorry,
end

end

end category_theory.abelian