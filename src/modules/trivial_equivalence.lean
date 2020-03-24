/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import linear_algebra.basic
import modules.modified_isomorphism_theorem

universes u u' u''

variables {R : Type u} [ring R]
variables (M : Type u') [add_comm_group M] [module R M]
variables (p : submodule R M)

noncomputable def equiv_quot_bot (h : p = ⊥) : M ≃ₗ[R] p.quotient :=
linear_equiv.of_bijective p.mkq (linear_map.ker_eq_bot'.2 $ λ x hx, by simpa [h] using hx)
  (submodule.range_mkq p)

noncomputable def equiv_top (h : p = ⊤) : p ≃ₗ[R] M :=
linear_equiv.of_bijective p.subtype (submodule.ker_subtype p)
  (linear_map.range_eq_top.2 $ λ x, ⟨⟨x, by rw h; trivial⟩, rfl⟩)

section
variables {M} {N : Type u''} [add_comm_group N] [module R N]
variables (f : M →ₗ[R] N) (h : f.ker = ⊥)

noncomputable def equiv_range_of_ker_bot : M ≃ₗ[R] f.range.mkq.ker :=
linear_equiv.trans (equiv_quot_bot M f.ker h) (quot_ker_equiv_range' f)

end

section
variables {M} {N : Type u''} [add_comm_group N] [module R N]
variables (f : M →ₗ[R] N) (h : f.range = ⊤)

noncomputable def equiv_range_of_range_top : f.ker.subtype.range.quotient ≃ₗ[R] N :=
linear_equiv.trans (quot_ker_equiv_range'' f) (equiv_top N f.range h)

end
