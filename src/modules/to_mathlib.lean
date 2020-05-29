import linear_algebra.basic

universes u v w x

variables {R : Type u} [ring R]
variables {M₁ : Type v} [add_comm_group M₁] [module R M₁]
variables {M₂ : Type w} [add_comm_group M₂] [module R M₂]
variables {M₃ : Type x} [add_comm_group M₃] [module R M₃]

open linear_map
open submodule

lemma linear_map.ker_le_range_iff {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} :
  g.ker ≤ f.range ↔ f.range.mkq.comp g.ker.subtype = 0 :=
by rw [←range_le_ker_iff, ker_mkq, range_subtype]

/-⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, mem_ker.2 $ by simpa using mem_range.1 (h x.2),
 λ h,
 begin
  rw ←range_le_ker_iff at h,
  rw ker_mkq at h,
  rw range_subtype at h,
  exact h,
 end-
  /-x hx,
 begin
  rw ←submodule.ker_mkq f.range,
  apply mem_ker.2,
  rw ←zero_apply x,
  rw ←h,
  --rw ←submodule.subtype_apply _ ⟨x, hx⟩,
  exact mem_ker.2 (@linear_map.congr _ _ _ _ _ _ _ _
    (comp (mkq (range f)) (submodule.subtype (ker g))) 0 ⟨x, hx⟩ h),-/
 end⟩-/
