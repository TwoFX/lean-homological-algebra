import linear_algebra.basic
import modified_isomorphism_theorem

universes u u' u''

variables {R : Type u} [ring R]
variables (M : Type u') [add_comm_group M] [module R M]
variables (p : submodule R M)

noncomputable def equiv_quot_bot : M ≃ₗ[R] (⊥ : submodule R M).quotient :=
linear_equiv.of_bijective (submodule.mkq ⊥) (submodule.ker_mkq _) (submodule.range_mkq _)

noncomputable def equiv_quot_bot' (h : p = ⊥) : M ≃ₗ[R] p.quotient :=
linear_equiv.of_bijective p.mkq
  (linear_map.ker_eq_bot'.2 $ λ x hx, by simpa [h] using hx)
  (submodule.range_mkq p)

lemma equiv_quot_bot_eq (h : p = ⊥) :
  (equiv_quot_bot' M p h).to_linear_map = p.mkq := rfl

variables {M} {N : Type u''} [add_comm_group N] [module R N]
variables (f : M →ₗ[R] N) (h : f.ker = ⊥)

noncomputable def equiv_range_of_ker_bot : M ≃ₗ[R] f.range :=
linear_equiv.trans (equiv_quot_bot' M f.ker h) (linear_map.quot_ker_equiv_range f)

noncomputable def equiv_range_of_ker_bot' : M ≃ₗ[R] f.range.mkq.ker :=
linear_equiv.trans (equiv_quot_bot' M f.ker h) (quot_ker_equiv_range' f)

@[simp] lemma equiv_range_of_ker_bot_map :
  (equiv_range_of_ker_bot f h).to_linear_map =
  (linear_map.quot_ker_equiv_range f).to_linear_map.comp
    (equiv_quot_bot' M f.ker h).to_linear_map :=
rfl

@[simp] lemma equiv_range_of_ker_bot_map' :
  (equiv_range_of_ker_bot' f h).to_linear_map =
  (quot_ker_equiv_range' f).to_linear_map.comp
    (equiv_quot_bot' M f.ker h).to_linear_map := rfl

lemma fac :
  f.range.subtype.comp (equiv_range_of_ker_bot f h).to_linear_map = f :=
linear_map.ext $ λ x, by erw [equiv_range_of_ker_bot_map, linear_map.comp_apply,
    submodule.subtype_apply, equiv_quot_bot_eq, ←linear_map.comp_apply,
    submodule.liftq_mkq, linear_map.cod_restrict_apply]

lemma fac' :
  f.range.mkq.ker.subtype.comp (equiv_range_of_ker_bot' f h).to_linear_map = f :=
linear_map.ext $ λ x, begin
  erw [equiv_range_of_ker_bot_map', linear_map.comp_apply], -- WTF??
end
