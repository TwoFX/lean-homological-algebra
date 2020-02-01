import linear_algebra.basic
import linear_algebra.direct_sum_module
import tactic.ring
open linear_map

--universes u v w x y z a
--variables {R : Type u} {A : Type v} {B : Type w} {C : Type x} { P : Type y} { N : Type z } { M : Type a }

section
variables {R : Type} {A : Type} {B : Type} {C : Type}
variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
variables [module R A] [module R B] [module R C]

lemma comp_vanish {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : range f ≤ ker g) : comp g f = 0 :=
by { ext, rw comp_apply, exact (iff.mp mem_ker) (h $ submodule.mem_map_of_mem trivial) }

lemma range_ker {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : comp g f = 0) : range f ≤ ker g :=
begin
  refine le_ker_iff_map.mpr _,
  ext,
  simp only [submodule.mem_map, mem_range, submodule.mem_bot],
  exact ⟨λ ⟨b, ⟨a, h₁⟩, h₂⟩,
    by { rw [←h₁, ←comp_apply, h, zero_apply] at h₂, exact eq.symm h₂, },
    λ h₁, ⟨0, ⟨⟨0, by simp⟩, by { rw map_zero, apply eq.symm, exact h₁ }⟩⟩⟩
end

end

section ses
  variables (R : Type) (A : Type) (B : Type) (C : Type)
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]
  structure ses :=
    (i : A →ₗ[R] B)
    (p : B →ₗ[R] C)
    (inj : ker i = ⊥)
    (exact : ker p = range i)
    (surj : range p = ⊤)

  structure right_split_ses extends ses R A B C :=
    (s : C →ₗ[R] B)
    (split : comp p s = (id : C →ₗ C))

  structure direct_sum_ses extends ses R A B C :=
    (b : (A × C) ≃ₗ[R] B)
    (comm_right : comp p (b : (A × C) →ₗ[R] B) = snd R A C)
    (comm_left : comp (b : (A × C) →ₗ[R] B) (inl R A C) = i)
end ses

section
  variables {R : Type} {A : Type} {B : Type} {C : Type}
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  lemma ses_vanish {s : ses R A B C} : comp s.p s.i = 0 :=
  by { refine comp_vanish _, rw s.exact, exact map_le_range, }

  @[simp] lemma ses_mem_vanish {s : ses R A B C} {a : A} : s.p (s.i a) = 0 :=
  by rw [←comp_apply, ses_vanish, zero_apply]

  lemma ses_pull {s : ses R A B C} {b : B} (h : s.p b = 0) : ∃ (a : A), s.i a = b :=
  mem_range.mp $ by { rw ←s.exact, exact mem_ker.mpr h, }

  @[simp] lemma right_split_apply {s : right_split_ses R A B C} {c : C} : s.p (s.s c) = c :=
  by rw [←comp_apply, s.split, id_apply]

  @[simp] lemma direct_sum_apply_right {s : direct_sum_ses R A B C} {a : A} {c : C} : s.p (s.b ⟨a, c⟩) = c :=
  by rw [←linear_equiv.coe_apply, ←comp_apply, s.comm_right, snd_apply]
end

variables {R : Type} {A : Type} {B : Type} {C : Type} {P : Type} {N : Type} {M : Type}

section splitting_lemma
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  noncomputable theorem direct_sum_of_right_split (r : right_split_ses R A B C) : direct_sum_ses R A B C :=
  let i := r.i, p := r.p, s := r.s in ⟨r.to_ses, linear_equiv.of_bijective (copair i s)
  begin
    apply ker_eq_bot'.mpr,
    rintros ⟨a, c⟩ h,
    have c₀ : c = 0, by { convert congr_arg p h; simp },
    have a₀ : a = 0, by { apply ker_eq_bot'.mp r.inj a, convert h, simp [c₀], },
    simpa [c₀, a₀],
  end
  begin
    rw [range_eq_top, function.surjective],
    intro b,
    have h : p (b - s (p b)) = 0, by simp,
    cases ses_pull h with a h₁,
    exact ⟨⟨a, p b⟩, by simp [h₁]⟩
  end,
  by { ext ⟨a, c⟩, rw [comp_apply, linear_equiv.coe_apply, linear_equiv.of_bijective_apply], simp, },
  by { ext a, rw [comp_apply, linear_equiv.coe_apply, linear_equiv.of_bijective_apply], simp, }⟩

  theorem right_split_of_direct_sum (r : direct_sum_ses R A B C) : right_split_ses R A B C :=
  ⟨r.to_ses, comp (r.b : (A × C) →ₗ[R] B) (inr R A C), by { ext c, simp, }⟩
end splitting_lemma

section projective
  structure mlift {R A B C : Type} [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
    [module R A] [module R B] [module R C] (f : A →ₗ[R] B) (g : C →ₗ[R] B) :=
    (h : C →ₗ[R] A)
    (comm : comp f h = g)

  class projective (R : Type) (P : Type) [ring R] [add_comm_group P] [module R P] :=
  (projectivity : Π {N : Type} {M : Type} [add_comm_group N] [add_comm_group M] [module R N] [module R M]
    (f : N →ₗ[R] M) (g : P →ₗ[R] M) (s : range f = ⊤), mlift f g)

  variables [ring R] [add_comm_group P] [module R P] [Pr : projective R P]
  variables [add_comm_group N] [add_comm_group M] [module R N] [module R M]
  variables (f : N →ₗ[R] M) (g : P →ₗ[R] M) (s : range f = ⊤)

  include Pr f g s

  theorem projectivity : mlift f g := projective.projectivity f g s
end projective

section
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C] 

  theorem projective_implies_right_split [projective R C]
    (h : ses R A B C) : right_split_ses R A B C :=
    let p := projectivity (h.p) id h.surj in ⟨h, p.h, p.comm⟩
end