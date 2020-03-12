import category_theory.category
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels

open category_theory
open category_theory.limits

universes v u

namespace category_theory.limits
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables {X Y : C} {f g : X ⟶ Y}

@[simp] lemma cofork.of_π_app_zero {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).ι.app walking_parallel_pair.zero = f ≫ π := rfl
@[simp] lemma cofork.of_π_app_one {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) :
  (cofork.of_π π w).ι.app walking_parallel_pair.one = π := rfl

end category_theory.limits

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

-- mathlib #2100

instance identity_is_epi (X : C) : epi.{v} (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩
instance (X : C) : mono.{v} (𝟙 X) :=
⟨λ Z g h w, by simpa using w⟩

instance epi_comp {X Y Z : C} (f : X ⟶ Y) [epi f] (g : Y ⟶ Z) [epi g] : epi (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_epi g).1,
  apply (cancel_epi f).1,
  simpa using w,
end
instance mono_comp {X Y Z : C} (f : X ⟶ Y) [mono f] (g : Y ⟶ Z) [mono g] : mono (f ≫ g) :=
begin
  split, intros Z a b w,
  apply (cancel_mono f).1,
  apply (cancel_mono g).1,
  simpa using w,
end

end

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

lemma kernel_fork_condition [has_zero_morphisms.{v} C] {P Q : C} {f : P ⟶ Q} (s : fork f 0) : fork.ι s ≫ f = 0 :=
begin
  rw fork.condition,
  erw has_zero_morphisms.comp_zero,
end

lemma kernel_fork_app_one [has_zero_morphisms.{v} C] {P Q : C} (f : P ⟶ Q) (s : fork f 0) :
  s.π.app walking_parallel_pair.one = 0 :=
begin
  rw ←cone_parallel_pair_right,
  erw has_zero_morphisms.comp_zero,
  refl,
end

lemma cokernel_cofork_app_zero [has_zero_morphisms.{v} C] {P Q : C} (f : P ⟶ Q) (s : cofork f 0) :
  s.ι.app walking_parallel_pair.zero = 0 :=
begin
  rw ←cocone_parallel_pair_right,
  erw has_zero_morphisms.zero_comp,
  refl,
end

section
variables [has_zero_morphisms.{v} C] {X Y : C} (f : X ⟶ Y)

abbreviation kernel_fork := fork f 0

def kernel_fork.of_ι {Z : C} (ι : Z ⟶ X) (h : ι ≫ f = 0) : kernel_fork f :=
fork.of_ι ι $ by rw [h, has_zero_morphisms.comp_zero]

def kernel.lift' [has_limit (parallel_pair f 0)]
  {Z : C} (g : Z ⟶ X) (h : g ≫ f = 0) : { l : Z ⟶ kernel f // l ≫ kernel.ι f = g} :=
⟨kernel.lift f g h, by erw limit.lift_π; refl⟩

abbreviation cokernel_cofork := cofork f 0

def cokernel_cofork.of_π {Z : C} (π : Y ⟶ Z) (h : f ≫ π = 0) : cokernel_cofork f :=
cofork.of_π π $ by rw [h, has_zero_morphisms.zero_comp]

def cokernel.desc' [has_colimit (parallel_pair f 0)]
  {Z : C} (g : Y ⟶ Z) (h : f ≫ g = 0) : { d : cokernel f ⟶ Z // cokernel.π f ≫ d = g } :=
⟨cokernel.desc f g h, by erw colimit.ι_desc; refl⟩

def cokernel.transport [has_colimit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
  is_colimit (cokernel_cofork.of_π l (cokernel.π f) $
  by rw [(iso.eq_inv_comp i).2 h, category.assoc, cokernel.condition, has_zero_morphisms.comp_zero]) :=
{ desc := λ s, cokernel.desc f (cofork.π s) $
    by erw [←h, category.assoc, cofork.condition,
    has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero],
  fac' := λ s j,
  begin
    cases j,
    { rw cokernel_cofork_app_zero,
      rw cokernel_cofork_app_zero,
      rw has_zero_morphisms.zero_comp,
      refl, },
    { erw colimit.ι_desc, refl, },
  end,
  uniq' := λ s m h,
  begin
    ext,
    rw colimit.ι_desc,
    exact h walking_parallel_pair.one,
  end }

end

end
