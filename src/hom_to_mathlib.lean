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

lemma cokernel_cofork_condition [has_zero_morphisms.{v} C] {P Q : C} {f : P ⟶ Q}
  (s : cofork f 0) : f ≫ cofork.π s = 0 :=
begin
  rw cofork.condition,
  erw has_zero_morphisms.zero_comp,
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

section

open category_theory.limits.walking_parallel_pair
open category_theory.limits.walking_parallel_pair_hom

variables {f} {g : X ⟶ Y}
def fork.is_limit.mk (t : fork f g)
  (lift : Π (s : cone (parallel_pair f g)), s.X ⟶ t.X)
  (fac : ∀ (s : cone (parallel_pair f g)), lift s ≫ t.π.app zero = s.π.app zero)
  (uniq : ∀ (s : cone (parallel_pair f g)) (m : s.X ⟶ t.X)
    (w : ∀ j : walking_parallel_pair, m ≫ t.π.app j = s.π.app j),
  m = lift s) : is_limit t :=
{ lift := lift,
  fac' := λ s j, walking_parallel_pair.cases_on j (fac s) $ by  
    rw [←s.w left, ←t.w left, ←category.assoc, fac],
  uniq' := uniq }

def cofork.is_colimit.mk (t : cofork f g)
  (desc : Π (s : cocone (parallel_pair f g)), t.X ⟶ s.X)
  (fac : ∀ (s : cocone (parallel_pair f g)),
    t.ι.app one ≫ desc s = s.ι.app one)
  (uniq : ∀ (s : cocone (parallel_pair f g)) (m : t.X ⟶ s.X)
    (w : ∀ j : walking_parallel_pair, t.ι.app j ≫ m = s.ι.app j),
  m = desc s) : is_colimit t :=
{ desc := desc,
  fac' := λ s j, walking_parallel_pair.cases_on j (by
    rw [←s.w left, ←t.w left, category.assoc, fac]) (fac s),
  uniq' := uniq }

end

def cokernel.transport [has_colimit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
  is_colimit (cokernel_cofork.of_π l (cokernel.π f) $
  by rw [(iso.eq_inv_comp i).2 h, category.assoc, cokernel.condition, has_zero_morphisms.comp_zero]) :=
cofork.is_colimit.mk _
  (λ s, cokernel.desc f (cofork.π s) $
    by erw [←h, category.assoc, cofork.condition,
    has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero])
   (λ s, by erw colimit.ι_desc; refl)
   (λ s m h, by ext; rw colimit.ι_desc; exact h walking_parallel_pair.one)

def kernel.transport [has_limit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f) (h : i.hom ≫ kernel.ι f = l) :
  is_limit (kernel_fork.of_ι f l $
    by rw [←h, category.assoc, kernel.condition, has_zero_morphisms.comp_zero]) :=
fork.is_limit.mk _
  (λ s, (kernel.lift f (fork.ι s) (kernel_fork_condition s)) ≫ i.inv)
  (λ s, begin
    rw category.assoc,
    erw (iso.inv_comp_eq i).2 h.symm,
    rw limit.lift_π,
    refl,
  end)
  (λ s m h', begin
    apply (iso.eq_comp_inv i).2,
    ext,
    simp only [limit.lift_π, fork.of_ι_app_zero, category.assoc],
    rw h,
    exact h' walking_parallel_pair.zero,
  end)

def cokernel.transport' [has_colimit (parallel_pair f 0)]
  {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z) (h : cokernel.π f ≫ i.hom = l) :
  is_colimit (cokernel_cofork.of_π f l $ 
    by rw [←h, ←category.assoc, cokernel.condition, has_zero_morphisms.zero_comp]) :=
cofork.is_colimit.mk _
  (λ s, i.inv ≫ (cokernel.desc f (cofork.π s) (cokernel_cofork_condition s)))
  (λ s, begin
    rw ←category.assoc,
    erw ←(iso.eq_comp_inv i).2 h,
    rw colimit.ι_desc,
    refl,
  end)
  (λ s m h', begin
    apply (iso.eq_inv_comp i).2,
    ext,
    simp only [category_theory.limits.cofork.of_π_app_one, colimit.ι_desc],
    rw ←category.assoc,
    rw h,
    exact h' walking_parallel_pair.one,
  end)

end

end
