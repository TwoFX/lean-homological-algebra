import category_theory.category
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.pullbacks

open category_theory
open category_theory.limits

universes v u
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

section
variables {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

def pullback.lift' [has_limit (cospan f g)] {W : C} (f' : W ⟶ X) (g' : W ⟶ Y)
  (h : f' ≫ f = g' ≫ g) :
  {l : W ⟶ pullback f g // l ≫ pullback.fst = f' ∧ l ≫ pullback.snd = g' } :=
⟨pullback.lift f' g' h, by erw limit.lift_π; refl, by erw limit.lift_π; refl⟩
end

section
variables [has_zero_morphisms.{v} C] {X Y : C} (f : X ⟶ Y)

def limit_kernel_fork.lift' {s : kernel_fork f} (is_lim : is_limit s)
  {Z : C} (g : Z ⟶ X) (h : g ≫ f = 0) :
  { l : Z ⟶ s.X // l ≫ fork.ι s = g } :=
⟨is_limit.lift is_lim $ kernel_fork.of_ι g h, by erw is_limit.fac; refl⟩

def colimit_cokernel_cofork.desc' {s : cokernel_cofork f} (is_colim : is_colimit s)
  {Z : C} (g : Y ⟶ Z) (h : f ≫ g = 0) :
  { l : s.X ⟶ Z // cofork.π s ≫ l = g } :=
⟨is_colimit.desc is_colim $ cokernel_cofork.of_π g h, by erw is_colimit.fac; refl⟩

end

section
variables [has_zero_morphisms.{v} C] {X Y : C} (f : X ⟶ Y)

def kernel.lift' [has_limit (parallel_pair f 0)]
  {Z : C} (g : Z ⟶ X) (h : g ≫ f = 0) : { l : Z ⟶ kernel f // l ≫ kernel.ι f = g} :=
⟨kernel.lift f g h, by erw limit.lift_π; refl⟩

def cokernel.desc' [has_colimit (parallel_pair f 0)]
  {Z : C} (g : Y ⟶ Z) (h : f ≫ g = 0) : { d : cokernel f ⟶ Z // cokernel.π f ≫ d = g } :=
⟨cokernel.desc f g h, by erw colimit.ι_desc; refl⟩


def cokernel.transport [has_colimit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
  is_colimit (cokernel_cofork.of_π (cokernel.π f) $ show l ≫ cokernel.π f = 0,
  by rw [(iso.eq_inv_comp i).2 h, category.assoc, cokernel.condition, has_zero_morphisms.comp_zero]) :=
cofork.is_colimit.mk _
  (λ s, cokernel.desc f (cofork.π s) $
    by erw [←h, category.assoc, cofork.condition,
    has_zero_morphisms.zero_comp, has_zero_morphisms.comp_zero])
   (λ s, by erw colimit.ι_desc; refl)
   (λ s m h, by ext; rw colimit.ι_desc; exact h walking_parallel_pair.one)

def kernel.transport [has_limit (parallel_pair f 0)]
  {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f) (h : i.hom ≫ kernel.ι f = l) :
  is_limit (kernel_fork.of_ι l $
    by rw [←h, category.assoc, kernel.condition, has_zero_morphisms.comp_zero]) :=
fork.is_limit.mk _
  (λ s, (kernel.lift f (fork.ι s) (kernel_fork.condition s)) ≫ i.inv)
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
  is_colimit (cokernel_cofork.of_π l $ 
    by rw [←h, ←category.assoc, cokernel.condition, has_zero_morphisms.zero_comp]) :=
cofork.is_colimit.mk _
  (λ s, i.inv ≫ (cokernel.desc f (cofork.π s) (cokernel_cofork.condition s)))
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
