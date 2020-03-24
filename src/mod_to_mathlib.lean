import linear_algebra.basic

universes u v w x

variables {R : Type u} [ring R]
variables {M₁ : Type v} [add_comm_group M₁] [module R M₁]
variables {M₂ : Type w} [add_comm_group M₂] [module R M₂]
variables {M₃ : Type x} [add_comm_group M₃] [module R M₃]

lemma range_le_ker_iff {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} : f.range ≤ g.ker ↔ g.comp f = 0 :=
⟨λ h, linear_map.ker_eq_top.1 $ submodule.eq_top_iff'.2 $ λ x, h $ submodule.mem_map_of_mem trivial,
  λ h x hx, linear_map.mem_ker.2 $ exists.elim hx $ λ y ⟨_, hy⟩,
    by rw [←hy, ←linear_map.comp_apply, h, linear_map.zero_apply]⟩

lemma linear_map.congr {f g : M₁ →ₗ[R] M₂} {x : M₁} : f = g → f x = g x :=
λ h, by rw h
