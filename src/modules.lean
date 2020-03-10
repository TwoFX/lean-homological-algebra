import algebra.category.Module.basic
import abelian

open category_theory
open category_theory.abelian
open category_theory.additive

universe u

variables (R : Type u) [ring R]

namespace Module

/-instance : abelian.{u} (Module.{u} R) :=
{ hom_group := by apply_instance,
  distrib_left' := λ P Q R f f' g,
    show (f + f') ≫ g = f ≫ g + f' ≫ g, by ext; simp,
  distrib_right' := λ P Q R f g g',
    show f ≫ (g + g') = f ≫ g + f ≫ g', by ext; simp,
  has_zero := by apply_instance,
  has_kernels := sorry,
  has_cokernels := sorry,
  epi_is_cokernel_of_kernel := sorry,
  mono_is_kernel_of_cokernel := sorry  }-/

end Module