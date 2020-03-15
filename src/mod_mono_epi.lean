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

lemma range_eq_top_of_cancel
  (h : ∀ (u v : N →ₗ[R] f.range.quotient), u.comp f = v.comp f → u = v) : f.range = ⊤ :=
begin
  have h₀ := h 0 f.range.mkq,
  have h₁ : (0 : N →ₗ[R] f.range.quotient).comp f = 0,
  { ext, simp, },
  have h₂ : f.range.mkq.comp f = 0 := comp_mkq f,
  have h₃ := h₀ (eq.trans h₁ h₂.symm),
  rw ←submodule.ker_mkq f.range,
  rw ←h₃,
  exact ker_zero,
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

lemma ker_eq_bot_of_mono' (h : mono f) : f.ker = ⊥ :=
ker_eq_bot_of_mono f

lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
begin
  apply range_eq_top_of_cancel,
  intros u v h,
  apply (@cancel_epi _ _ _ _ _ f _ (up u) (up v)).1,
  exact h,
end

lemma mono_of_ker_eq_bot (hf : f.ker = ⊥) : mono f :=
⟨λ Z u v h, begin
  ext,
  apply (linear_map.ker_eq_bot.1 hf),
  rw ←linear_map.comp_apply,
  change (u ≫ f) x = f (v x),
  rw h,
  refl,
end⟩

lemma epi_of_range_eq_top (hf : f.range = ⊤) : epi f :=
⟨λ Z u v h, begin
  ext,
  cases linear_map.range_eq_top.1 hf x with y hy,
  rw ←hy,
  rw ←linear_map.comp_apply,
  change (f ≫ u) y = v (f y),
  rw h,
  refl,
end⟩

end category