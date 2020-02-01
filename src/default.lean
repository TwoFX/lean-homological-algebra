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
    rintro ⟨a, c⟩,
    rw copair_apply,
    intro h,
    have c₀ : c = 0, by { have h₁ := congr_arg p h, simp at h₁, exact h₁ },
    have a₀ : a = 0, by { rw c₀ at h, rw [map_zero, add_zero, ←map_zero i] at h, exact (ker_eq_bot.mp r.inj) h, },
    simpa [c₀, a₀],
  end
  begin
    rw [range_eq_top, function.surjective],
    intro b,
    have h : p (b - s (p b)) = 0, by simp,
    cases ses_pull h with a h₁,
    simp only [prod.exists, copair_apply],
    exact ⟨a, p b, by { rw h₁, simp, }⟩
  end,
  by { ext ⟨a, c⟩, rw [comp_apply, linear_equiv.coe_apply, linear_equiv.of_bijective_apply], simp, },
  by { ext a, rw [comp_apply, linear_equiv.coe_apply, linear_equiv.of_bijective_apply], simp, }⟩

  theorem right_split_of_direct_sum (r : direct_sum_ses R A B C) : right_split_ses R A B C :=
  ⟨r.to_ses, comp (r.b : (A × C) →ₗ[R] B) (inr R A C), by { ext c, simp, }⟩
  /-noncomputable theorem right_split_implies_direct_sum (r : right_split_ses R A B C) : direct_sum_ses R A B C :=
  ⟨⟨r.i, r.p, r.inj, r.exact, r.surj⟩, begin
    fapply linear_equiv.of_bijective, exact copair r.i r.s,
    rw ker_eq_bot', intros ac m0,
    have a : (ac.fst, ac.snd) = ac := by apply prod.mk.eta,
    rw ←a at m0, rw copair_apply at m0,
    have b : ac.snd = 0 :=
    begin
      have m1 := congr_arg r.p m0, simp at m1,
      have in_ker : r.i ac.fst ∈ ker r.p := by 
        { rw r.exact, rw mem_range, exact exists.intro ac.fst rfl, },
      simp at in_ker, rw in_ker at m1, simp at m1,
      rw ←comp_apply at m1, rw r.split at m1, simp at m1,
      assumption,
    end, rw b at m0, simp at m0,
    rw ←mem_ker at m0, rw r.inj at m0, simp at m0,
    rw ←a, rw b, rw m0,
    have z : ((0 : A × C).fst, (0 : A × C).snd) = (0 : A × C) := by apply prod.mk.eta,
    rw ←z, rw prod.fst_zero, rw prod.snd_zero,
    ext, rw mem_range, split, intro, simp,
    intro, rename x b,
    have in_ker : b - r.s (r.p b) ∈ ker r.p :=
      by { simp, rw ←comp_apply, rw r.split, simp, },
    rw r.exact at in_ker, rw mem_range at in_ker,
    cases in_ker with a ha,
    fapply exists.intro, exact (a, r.p b),
    simp, safe,
  end⟩-/
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

    /-begin
    unfold is_ses at h,
    cases h with ex out, cases out with inj sur,
    have u := projectivity g (linear_map.id : C →ₗ[R] C) sur,
    cases u with h hh,
    unfold split_right,
    fapply exists.intro,
    exact h, symmetry, assumption,
  end-/ 
end





--set_option pp.universes true

section exact
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  def exact_at (f : A →ₗ[R] B) (g : B →ₗ[R] C) : Prop := ker g = range f
  @[simp] lemma exact_iff (f : A →ₗ[R] B) (g : B →ₗ[R] C) : exact_at f g ↔ ker g = range f
  := by refl
end exact

section exact
  variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  variables [module R A] [module R B] [module R C]

  def is_ses (f : A →ₗ[R] B) (g : B →ₗ[R] C) : Prop :=
    exact_at f g ∧ ker f = ⊥ ∧ range g = ⊤

  def split_right (f : A →ₗ[R] B) (g : B →ₗ[R] C) : Prop :=
    ∃ (s : C →ₗ[R] B), comp g s = (id : C →ₗ[R] C)

  
end exact



section mult
    variable [ring R]

    def f : R → R → R := λ n x, x * n
    lemma f_eq (n : R) (x : R) : f n x = x * n := rfl
    def mult_is_linear (n : R) : is_linear_map R (f n) :=
    by { constructor; simp [f_eq]; intros, rw right_distrib, rw mul_assoc, }
end mult

section integral
  variables [integral_domain R]

  def mult (n : R) : R →ₗ[R] R := is_linear_map.mk' (f n) (mult_is_linear n)
  lemma mult_eq (n : R) : mult n = is_linear_map.mk' (f n) (mult_is_linear n)
  := rfl

  lemma mult_has_trivial_kernel (n : R) (h : n ≠ 0) : ker (mult n) = ⊥ :=
  begin
    ext, rw mem_ker, rw mult_eq, simp, rw f_eq,
    rw mul_eq_zero_iff_eq_zero_or_eq_zero, split,
    intro H, cases H, exact H, contradiction, intros, left, exact a,
  end

  def nR (n : R) : submodule R R := submodule.span R { n }
  lemma nR_eq (n : R) : nR n = submodule.span R { n } := rfl
  def myproj (n : R) : R →ₗ[R] (nR n).quotient := submodule.mkq (nR n)
  lemma proj_eq (n : R) : myproj n = submodule.mkq (nR n) := rfl

  theorem mult_is_ses (n : R) (h : n ≠ 0) : is_ses (mult n) (myproj n) :=
  begin
    constructor, simp, ext, simp, rw mult_eq, simp, simp [f_eq],
    rw proj_eq, simp, rw nR_eq, split,
    intros, refine submodule.span_induction a _ _ _ _,
    intros, simp at H, fapply exists.intro, exact 1, ring, symmetry,
    exact H, fapply exists.intro, exact 0, ring, intros,
    cases a_1 with y1 yp, cases a_2 with y2 y2p, fapply exists.intro,
    exact y1 + y2, rw [right_distrib, yp, y2p], intros,
    cases a_2 with y yp, rw ←yp, simp, rw ←mul_assoc,
    fapply exists.intro, exact a_1 * y, refl, intro,
    cases a with y hy, rw ←hy, rw ←smul_eq_mul,
    refine submodule.smul_mem _ _ _,
    unfold_projs, unfold_coes,
    rw ←set.singleton_subset_iff,
    exact submodule.subset_span,
    split, exact mult_has_trivial_kernel _ h,
    ext, rw proj_eq, simp, 
  end
end integral