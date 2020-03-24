import linear_algebra.basic

universes u v w x

variables {R : Type u} [ring R]
variables {M₁ : Type v} [add_comm_group M₁] [module R M₁]
variables {M₂ : Type w} [add_comm_group M₂] [module R M₂]
variables {M₃ : Type x} [add_comm_group M₃] [module R M₃]

open linear_map
open submodule

lemma linear_map.congr {f g : M₁ →ₗ[R] M₂} (x : M₁) : f = g → f x = g x :=
λ h, by rw h

lemma linear_map.ker_le_range_iff {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} :
  g.ker ≤ f.range ↔ f.range.mkq.comp g.ker.subtype = 0 :=
⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, mem_ker.2 $ by simp; exact mem_range.1 (h x.2),
 λ h x hx,
 begin
  rw ←submodule.ker_mkq f.range,
  exact mem_ker.2 (@linear_map.congr _ _ _ _ _ _ _ _
    (comp (mkq (range f)) (submodule.subtype (ker g))) 0 ⟨x, hx⟩ h),
 end⟩
