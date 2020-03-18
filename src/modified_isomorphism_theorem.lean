/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import linear_algebra.basic

open linear_map

/- The following is taken from linear_algebra/basic.lean and modified. -/

universes u v w
variables {R : Type u} {M : Type v} {M₂ : Type w}
variables [ring R] [add_comm_group M] [add_comm_group M₂]
variables [module R M] [module R M₂]
variables (f : M →ₗ[R] M₂)

/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`, or put differently, to the kernel of the quotient map by the
range of `f`.  -/
noncomputable def quot_ker_equiv_range' : f.ker.quotient ≃ₗ[R] f.range.mkq.ker :=
have hr : ∀ x : f.range, ∃ y, f y = ↑x := λ x, x.2.imp $ λ _, and.right,
have hr' : ∀ x : f.range.mkq.ker, ∃ y, f y = x := begin
  rw submodule.ker_mkq f.range,
  exact hr,
end,
let F : f.ker.quotient →ₗ[R] f.range.mkq.ker :=
  f.ker.liftq (cod_restrict f.range.mkq.ker f $
    begin
      intro x,
      rw submodule.ker_mkq f.range,
      exact submodule.mem_map_of_mem trivial,
    end)
    (λ x hx, by simp; apply subtype.coe_ext.2; simpa using hx) in
{ inv_fun    := λx, submodule.quotient.mk (classical.some (hr' x)),
  left_inv   := by rintro ⟨x⟩; exact
    (submodule.quotient.eq _).2 (sub_mem_ker_iff.2 $
      classical.some_spec $ hr' $ F $ submodule.quotient.mk x),
  right_inv  := λ x : f.range.mkq.ker, subtype.eq $ classical.some_spec (hr' x),
  .. F }

noncomputable def quot_ker_equiv_range'' : f.ker.subtype.range.quotient ≃ₗ[R] f.range :=
have hr : ∀ x : f.range, ∃ y, f y = ↑x := λ x, x.2.imp $ λ _, and.right,
let F : f.ker.subtype.range.quotient →ₗ[R] f.range :=
  f.ker.subtype.range.liftq (cod_restrict f.range f $ λ x, ⟨x, trivial, rfl⟩)
    (λ x hx, by simp; apply subtype.coe_ext.2; simpa using hx) in
{ inv_fun    := λx, submodule.quotient.mk (classical.some (hr x)),
  left_inv   := begin
    rintro ⟨x⟩,
    simp,
    apply (submodule.quotient.eq _).2,
    simp only [submodule.range_subtype],
    exact (sub_mem_ker_iff.2 $
      classical.some_spec $ hr $ F $ submodule.quotient.mk x),
    end,
  right_inv  := λ x : range f, subtype.eq $ classical.some_spec (hr x),
  .. F }