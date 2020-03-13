import linear_algebra.basic
import algebra.category.Module.basic

section linear_map
universes u u' u''
variables {R : Type u} [ring R]
variables {M : Type u'} [add_comm_group M] [module R M]
variables {N : Type u''} [add_comm_group N] [module R N]

open linear_map
variables (f : M →ₗ[R] N)

lemma ker_comp : f.comp (f.ker).subtype = 0 :=
linear_map.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

lemma comp_mkq : f.range.mkq.comp f = 0 :=
linear_map.ext $ λ x, by simp; use x

lemma ker_eq_bot_of_cancel (h : ∀ (u v : f.ker →ₗ[R] M), f.comp u = f.comp v → u = v) :
  f.ker = ⊥ :=
begin
  have h₀ := h 0 f.ker.subtype,
  have h₁ : f.comp (0 : f.ker →ₗ[R] M) = 0,
  { ext, simp, },
  have h₂ : f.comp f.ker.subtype = 0 := ker_comp f,
  have h₃ := h₀ (eq.trans h₁ h₂.symm),
  rw ←submodule.range_subtype f.ker,
  rw ←h₃,
  exact submodule.map_zero ⊤,
end

end linear_map

section category
universes u

variables {R : Type u} [ring R]
variables {M N : Module R}


open category_theory Module

section

variables {A : Type u} {B : Type u} [add_comm_group A] [add_comm_group B] [module R A] [module R B]

def up (g : A →ₗ[R] B) : (of R A) ⟶ (of R B) := g

def up_equiv (g : A ≃ₗ[R] B) : (of R A) ≅ (of R B) :=
{ hom := up g,
  inv := up g.symm,
  hom_inv_id' :=
  begin
    ext,
    simp only [function.comp_app, id_apply, Module.coe_comp],
    erw linear_equiv.symm_apply_apply,
  end,
  inv_hom_id' :=
  begin
    ext,
    simp only [function.comp_app, id_apply, Module.coe_comp],
    erw linear_equiv.apply_symm_apply,
  end }

end

section
variables {A B : Module R}

def up_equiv' (g : A ≃ₗ[R] B) : A ≅ B :=
{ hom := g,
  inv := g.symm,
  hom_inv_id' :=
  begin
    ext,
    simp only [linear_equiv.coe_apply, function.comp_app, id_apply, Module.coe_comp],
    erw linear_equiv.symm_apply_apply,
  end,
  inv_hom_id' :=
  begin
    ext,
    simp only [linear_equiv.coe_apply, function.comp_app, id_apply, Module.coe_comp],
    erw linear_equiv.apply_symm_apply,
  end }
end

variables (f : M ⟶ N)

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
begin
  apply ker_eq_bot_of_cancel,
  intros u v h,
  apply (@cancel_mono _ _ _ _ _ f _ (up u) (up v)).1,
  exact h,
end

end category