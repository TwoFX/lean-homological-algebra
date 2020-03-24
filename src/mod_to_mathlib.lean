import linear_algebra.basic

universes u v w x

variables {R : Type u} [ring R]
variables {M₁ : Type v} [add_comm_group M₁] [module R M₁]
variables {M₂ : Type w} [add_comm_group M₂] [module R M₂]
variables {M₃ : Type x} [add_comm_group M₃] [module R M₃]

lemma linear_map.congr {f g : M₁ →ₗ[R] M₂} {x : M₁} : f = g → f x = g x :=
λ h, by rw h
