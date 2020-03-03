import linear_algebra.basic diagram_chase

open linear_map

section part_one
variables {R : Type*} [ring R]
variables {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
variables [add_comm_group A] [add_comm_group B] [add_comm_group A'] [add_comm_group B']
variables [module R A] [module R B] [module R A'] [module R B']
variables {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {α : A →ₗ[R] A'} {β : B →ₗ[R] B'}
variables (comm : g ∘ α = β ∘ f)
include comm

set_option profiler true

lemma nine₁ (hg : ker g = ⊥) (hα : ker α = ⊥) (hβ : ker β = ⊥) : ker f = ⊥ :=
ker_eq_bot'.2 $ λ a ha, by chase a [ha] using [α] with a' only 0 = 0

lemma nnine₁ (hg : ker g = ⊥) (hα : ker α = ⊥) (hβ : ker β = ⊥) : ker f = ⊥ :=
ker_eq_bot'.2 $ λ a ha, ker_eq_bot'.1 hα a $ ker_eq_bot'.1 hg (α a) $
by rw [←function.comp_apply g α, comm]; simp [ha]

end part_one