import category_theory.category
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.zero

open category_theory
open category_theory.limits

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