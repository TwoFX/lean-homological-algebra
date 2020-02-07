/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel.

Short exact sequences of modules over a ring.
-/
import linear_algebra.basic
open linear_map

/-!
# Short exact sequences

This file defines short exact sequenes of modules over a ring.

If R is a ring and ... → Mᵢ₊₁ → Mᵢ → Mᵢ₋₁ → ...  is a squence of modules
over R and linear maps fᵢ : Mᵢ → Mᵢ₋₁, then the sequence is called exact
at Mᵢ if range fᵢ₊₁ = ker fᵢ. The sequence is called exact if it is exact at
every Mᵢ. A short exact sequence is the special case where Mᵢ = 0 for
i < 0 or i > 2. It is often written as 0 → A → B → C → 0.  If the maps are
i : A → B and p : B → C, then the short exact sequence condition asserts
three things:

* i is injective
* range i = ker p
* p is surjective

## Main definitions


## Main statements

## Implementation notes
The splitting lemma states that once we have an instance of left_split_short_exact,
right_split_short_exact, or direct_sum_short_exact, we may promote it to the
universal split_exact_sequence.
-/

section
variables {R : Type*} {A : Type*} {B : Type*} {C : Type*}
variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
variables [module R A] [module R B] [module R C]

lemma comp_vanish {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : range f ≤ ker g) : comp g f = 0 :=
by { ext, rw comp_apply, exact mem_ker.1 (h $ submodule.mem_map_of_mem trivial) }

end

section short_exact
variables (R : Type*) (A : Type*) (B : Type*) (C : Type*)
variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
variables [module R A] [module R B] [module R C]

/--
A short exact sequence of modules
-/
structure short_exact :=
(i : A →ₗ[R] B)
(p : B →ₗ[R] C)
(inj : ker i = ⊥)
(exact : ker p = range i)
(surj : range p = ⊤)
end short_exact

namespace short_exact
variables {R : Type*} {A : Type*} {B : Type*} {C : Type*}
variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
variables [module R A] [module R B] [module R C]

lemma vanish {s : short_exact R A B C} : comp s.p s.i = 0 :=
by { refine comp_vanish _, rw s.exact, exact map_le_range }

@[simp] lemma mem_vanish {s : short_exact R A B C} {a : A} : s.p (s.i a) = 0 :=
by rw [←comp_apply, vanish, zero_apply]

lemma pull {s : short_exact R A B C} {b : B} (h : s.p b = 0) : ∃ (a : A), s.i a = b :=
mem_range.1 $ by { rw ←s.exact, exact mem_ker.2 h }

/--
For every surjective linear map f there is a canonical associated short exact sequence
0 → ker f → A → B → 0.
-/
def of_surj (f : A →ₗ[R] B) (h : range f = ⊤) : short_exact R _ A B :=
⟨(ker f).subtype, f, submodule.ker_subtype (ker f), (submodule.range_subtype (ker f)).symm, h⟩

/--
For every injective linear map f there is a canonical associated short exact sequence
0 → A → B → coker f → 0.
-/
def of_inj (f : A →ₗ[R] B) (h : ker f = ⊥) : short_exact R A B _ :=
⟨f, (range f).mkq, h, submodule.ker_mkq (range f), submodule.range_mkq (range f)⟩
end short_exact

section split
variables (R : Type*) (A : Type*) (B : Type*) (C : Type*)
variables [ring R] [add_comm_group A] [add_comm_group B] [add_comm_group C]
variables [module R A] [module R B] [module R C]

structure left_split_short_exact extends short_exact R A B C :=
(t : B →ₗ[R] A)
(splitl : comp t i = (id : A →ₗ[R] A))

structure right_split_short_exact extends short_exact R A B C :=
(s : C →ₗ[R] B)
(splitr : comp p s = (id : C →ₗ[R] C))

structure direct_sum_short_exact extends short_exact R A B C :=
(b : (A × C) ≃ₗ[R] B)
(commr : comp p (b : (A × C) →ₗ[R] B) = snd R A C)
(comml : comp (b : (A × C) →ₗ[R] B) (inl R A C) = i)

structure split_short_exact extends short_exact R A B C :=
(t : B →ₗ[R] A)
(s : C →ₗ[R] B)
(b : (A × C) ≃ₗ[R] B)
(splitr : comp p s = (id : C →ₗ[R] C))
(splitl : comp t i = (id : A →ₗ[R] A))
(commr : comp p (b : (A × C) →ₗ[R] B) = snd R A C)
(comml : comp (b : (A × C) →ₗ[R] B) (inl R A C) = i)
end split