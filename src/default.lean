import linear_algebra.basic
import linear_algebra.basis
import linear_algebra.direct_sum_module
open linear_map

--universes u v w x y z a
--variables {R : Type u} {A : Type v} {B : Type w} {C : Type x} { P : Type y} { N : Type z } { M : Type a }

section
  variables {R : Type} {A : Type} {B : Type} {C : Type}
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  lemma symm_mover {f : A ≃ₗ[R] B} {g : B →ₗ[R] C} {h : A →ₗ[R] C} (h₁ : h = comp g f) : comp h (f.symm : B →ₗ[R] A) = g :=
  by { ext, rw h₁, simp only [comp_apply, linear_equiv.coe_apply, linear_equiv.apply_symm_apply], }

  lemma symm_movel {f : B ≃ₗ[R] C} {g : A →ₗ[R] B} {h : A →ₗ[R] C} (h₁ : h = comp (f : B →ₗ[R] C) g) : comp (f.symm : C →ₗ[R] B) h = g :=
  by { ext, rw h₁, simp only [comp_apply, linear_equiv.coe_apply, linear_equiv.symm_apply_apply], }

  lemma comp_vanish {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : range f ≤ ker g) : comp g f = 0 :=
  by { ext, rw comp_apply, exact mem_ker.1 (h $ submodule.mem_map_of_mem trivial) }

  lemma range_ker {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : comp g f = 0) : range f ≤ ker g :=
  begin
    refine le_ker_iff_map.2 _,
    ext,
    simp only [submodule.mem_map, mem_range, submodule.mem_bot],
    exact ⟨λ ⟨b, ⟨a, h₁⟩, h₂⟩,
      by { rw [←h₁, ←comp_apply, h, zero_apply] at h₂, exact h₂.symm, },
      λ h₁, ⟨0, ⟨⟨0, by simp⟩, by { rw map_zero, exact h₁.symm }⟩⟩⟩
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

  structure left_split_ses extends ses R A B C :=
    (t : B →ₗ[R] A)
    (splitl : comp t i = (id : A →ₗ[R] A))

  structure right_split_ses extends ses R A B C :=
    (s : C →ₗ[R] B)
    (splitr : comp p s = (id : C →ₗ[R] C))

  structure direct_sum_ses extends ses R A B C :=
    (b : (A × C) ≃ₗ[R] B)
    (commr : comp p (b : (A × C) →ₗ[R] B) = snd R A C)
    (comml : comp (b : (A × C) →ₗ[R] B) (inl R A C) = i)

  structure split_ses extends ses R A B C :=
    (t : B →ₗ[R] A)
    (s : C →ₗ[R] B)
    (b : (A × C) ≃ₗ[R] B)
    (splitr : comp p s = (id : C →ₗ[R] C))
    (splitl : comp t i = (id : A →ₗ[R] A))
    (commr : comp p (b : (A × C) →ₗ[R] B) = snd R A C)
    (comml : comp (b : (A × C) →ₗ[R] B) (inl R A C) = i)

end ses

section ses
  variables {R : Type} {A : Type} {B : Type} {C : Type}
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  lemma ses_vanish {s : ses R A B C} : comp s.p s.i = 0 :=
  by { refine comp_vanish _, rw s.exact, exact map_le_range, }

  @[simp] lemma ses_mem_vanish {s : ses R A B C} {a : A} : s.p (s.i a) = 0 :=
  by rw [←comp_apply, ses_vanish, zero_apply]

  lemma ses_pull {s : ses R A B C} {b : B} (h : s.p b = 0) : ∃ (a : A), s.i a = b :=
  mem_range.1 $ by { rw ←s.exact, exact mem_ker.2 h, }

  @[simp] lemma left_split_apply {s : left_split_ses R A B C} { a : A} : s.t (s.i a) = a :=
  by rw [←comp_apply, s.splitl, id_apply]

  @[simp] lemma right_split_apply {s : right_split_ses R A B C} {c : C} : s.p (s.s c) = c :=
  by rw [←comp_apply, s.splitr, id_apply]

  @[simp] lemma direct_sum_apply_right {s : direct_sum_ses R A B C} {a : A} {c : C} : s.p (s.b ⟨a, c⟩) = c :=
  by rw [←linear_equiv.coe_apply, ←comp_apply, s.commr, snd_apply]

  @[simp] lemma direct_sum_apply_left {s : direct_sum_ses R A B C} {a : A} : s.b (a, 0) = s.i a :=
  begin
    have : (a, 0) = (inl R A C) a := by simp,
    rw [←linear_equiv.coe_apply, this, ←comp_apply, s.comml],
  end
end ses

section ses
  variables {R : Type} {A : Type} {B : Type} {C : Type}
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  def of_surj (f : A →ₗ[R] B) (h : range f = ⊤) : ses R (ker f) A B :=
  ⟨(ker f).subtype, f, submodule.ker_subtype (ker f), (submodule.range_subtype (ker f)).symm, h⟩
end ses

variables {R : Type} {A : Type} {B : Type} {C : Type} {P : Type} {N : Type} {M : Type}

section splitting_lemma
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]
  
  private noncomputable def direct_sum_of_left_split (r : left_split_ses R A B C) : direct_sum_ses R A B C :=
  let i := r.i, p := r.p, t := r.t, b := linear_equiv.of_bijective (pair t p)
  begin
    apply ker_eq_bot'.2,
    intros b h,
    have h₁ : t b = 0 ∧ p b = 0, by simpa using prod.mk.inj h,
    cases ses_pull h₁.2 with a h₂,
    have h₃ : a = t b, by simpa using (congr_arg t h₂),
    simpa [h₃, h₁.1] using h₂.symm,
  end
  begin
    rw [range_eq_top, function.surjective],
    rintro ⟨a, c⟩,
    cases range_eq_top.1 r.surj c with b h,
    exact ⟨i a + b - i (t b), by simp [h]⟩
  end
  in ⟨r.to_ses, b.symm,
  begin
    apply symm_mover,
    ext,
    rw [comp_apply, linear_equiv.coe_apply, linear_equiv.of_bijective_apply],
    simp,
  end,
  begin
    apply symm_movel,
    ext1,
    rw [comp_apply, linear_equiv.coe_apply, linear_equiv.of_bijective_apply],
    simp,
  end⟩

  private def left_split_of_direct_sum (r : direct_sum_ses R A B C) : left_split_ses R A B C :=
  ⟨r.to_ses, comp (fst R A C) (r.b.symm), begin
    ext,
    rw [comp_apply, comp_apply, ←direct_sum_apply_left,
      linear_equiv.coe_apply, linear_equiv.symm_apply_apply],
    simp,
  end⟩

  private noncomputable def direct_sum_of_right_split (r : right_split_ses R A B C) : direct_sum_ses R A B C :=
  let i := r.i, p := r.p, s := r.s in ⟨r.to_ses, linear_equiv.of_bijective (copair i s)
  begin
    apply ker_eq_bot'.2,
    rintros ⟨a, c⟩ h,
    have c₀ : c = 0, by simpa using congr_arg p h,
    have a₀ : a = 0, by { apply ker_eq_bot'.1 r.inj a, convert h, simp [c₀], },
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

  private def right_split_of_direct_sum (r : direct_sum_ses R A B C) : right_split_ses R A B C :=
  ⟨r.to_ses, comp (r.b : (A × C) →ₗ[R] B) (inr R A C), by { ext c, simp, }⟩

  def split_of_direct_sum (d : direct_sum_ses R A B C) : split_ses R A B C :=
  let l := left_split_of_direct_sum d, r := right_split_of_direct_sum d in
  ⟨d.to_ses, l.t, r.s, d.b, r.splitr, l.splitl, d.commr, d.comml⟩

  noncomputable def split_of_right_split (r : right_split_ses R A B C) : split_ses R A B C :=
  let d := direct_sum_of_right_split r, l := left_split_of_direct_sum d in
  ⟨r.to_ses, l.t, r.s, d.b, r.splitr, l.splitl, d.commr, d.comml⟩

  noncomputable def split_of_left_split (l : left_split_ses R A B C) : split_ses R A B C :=
  let d := direct_sum_of_left_split l, r := right_split_of_direct_sum d in
  ⟨l.to_ses, l.t, r.s, d.b, r.splitr, l.splitl, d.commr, d.comml⟩
end splitting_lemma

section free
  class free (R : Type) (M : Type) [ring R] [add_comm_group M] [module R M] :=
  (ι : Type)
  (v : ι → M)
  (bas : is_basis R v)
end free

section projective

  class projective (R : Type) (P : Type) [ring R] [add_comm_group P] [module R P] :=
  (projectivity : Π {N : Type} {M : Type} [add_comm_group N] [add_comm_group M] [module R N] [module R M]
    (f : N →ₗ[R] M) (g : P →ₗ[R] M) (s : range f = ⊤), ∃ (h : P →ₗ[R] N), comp f h = g)

  variables [ring R] [add_comm_group P] [module R P] [Pr : projective R P]
  variables [add_comm_group N] [add_comm_group M] [module R N] [module R M]
  variables (f : N →ₗ[R] M) (g : P →ₗ[R] M) (s : range f = ⊤)

  include Pr f g s

  theorem projectivity : ∃ (h : P →ₗ[R] N), comp f h = g := projective.projectivity f g s
end projective

set_option pp.proofs true

section free
  variables [ring R] [add_comm_group P] [module R P]
  theorem from_free [h : free R P] : (projective R P) :=
  ⟨begin
    introsI,
    exact ⟨begin
      refine is_basis.constr h.bas _,
      intro i,
      have u := range_eq_top.1 s (g (@free.v R P _ _ _ h i)),
      exact classical.some u,
    end,
    begin
      apply is_basis.ext h.bas _,
      intro i,
      rw [comp_apply, is_basis.constr_apply],
      simp only [finsupp_sum, map_smul],
      rw [is_basis.repr_eq_single],
      rw finsupp.sum_single_index; simp,
      rw classical.some_spec (range_eq_top.1 s (g (@free.v R P _ _ _ h i))),
    end⟩
  end⟩
end free


section
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C] 

  noncomputable theorem projective_implies_right_split [projective R C]
    (h : ses R A B C) : right_split_ses R A B C :=
    let p := classical.indefinite_description _ (projectivity h.p id h.surj) in ⟨h, p.1, p.2⟩
end