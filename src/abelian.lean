import category_theory.category zero kernel category_theory.limits.shapes.binary_products category_theory.isomorphism

universes v u

open category_theory
open category_theory.limits

namespace category_theory.abelian

section
variables {C : Type u} [𝒞 : category.{v} C] [has_zero_object.{v} C]
variables {P Q : C} (f : P ⟶ Q) 
include 𝒞

class regular_mono [mono f] :=
(R : C)
(g : Q ⟶ R)
(w : f ≫ g = ∅)
(is_kernel : is_limit (fork.of_ι f (by {rw ←comp_zero _ f at w, exact w}) : fork g ∅))

class regular_epi [epi f] :=
(O : C)
(g : O ⟶ P)
(w : g ≫ f = ∅)
(is_cokernel : is_colimit (cofork.of_π f (by {rw ←zero_comp _ f at w, exact w}) : cofork g ∅))

end

section
variables (C : Type u)

class abelian_category [category.{v} C] [has_zero_object.{v} C] [has_binary_products.{v} C]
    [has_binary_coproducts.{v} C] [has_kernels.{v} C] [has_cokernels.{v} C] :=
(monos_are_kernels : ∀ {P Q : C} (f : P ⟶ Q) [mono f], regular_mono.{v} f)
(epis_are_cokernels : ∀ {P Q : C} (f : P ⟶ Q) [epi f], regular_epi.{v} f)

end

section
variables {C : Type u} [𝒞 : category.{v} C] [has_zero_object.{v} C] [has_binary_products.{v} C]
variables [has_binary_coproducts.{v} C] [has_kernels.{v} C] [has_cokernels.{v} C] [abelian_category.{v} C]
include 𝒞

lemma mono_epi_iso {P Q : C} (f : P ⟶ Q) [mono f] [epi f] : is_iso f :=
begin
  have r := abelian_category.monos_are_kernels f,
  have : r.g = ∅ := comp_zero' r.w,
  have c : is_limit (fork.of_ι f (by simp) : fork (∅ : Q ⟶ r.R) ∅) := begin
    convert r.is_kernel; exact this.symm,
  end,
  have d : is_limit (fork.of_ι (𝟙 Q) rfl : fork (∅ : Q ⟶ r.R) ∅)
    := @limit.is_limit _ _ _ _ _ (ker_eq_id.{v} Q r.R).to_has_limit,
  let e := is_limit.unique_up_to_iso.{v} c d,
  let v := functor.map_iso cones.forget e,
  let w := is_iso.of_iso v,
  simp at w,
  let h := cone_morphism.w e.hom walking_parallel_pair.zero,
  simp at h,
  haveI : is_iso (𝟙 Q) := by apply_instance,
  rw ←h,
  apply_instance,
end

end

end category_theory.abelian