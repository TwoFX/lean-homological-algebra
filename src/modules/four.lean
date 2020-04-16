/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import linear_algebra.basic
import modules.modules
import diagram_lemmas

open linear_map
open Module

universe u

section four
variables {R : Type u} [ring R]
variables {A : Type u} {B : Type u} {C : Type u} {D : Type u}
variables [add_comm_group A] [add_comm_group B] [add_comm_group C] [add_comm_group D]
variables [module R A] [module R B] [module R C] [module R D]
variables {A' : Type u} {B' : Type u} {C' : Type u} {D' : Type u}
variables [add_comm_group A'] [add_comm_group B'] [add_comm_group C'] [add_comm_group D']
variables [module R A'] [module R B'] [module R C'] [module R D']
variables {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D}
variables {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'} {h' : C' →ₗ[R] D'}
variables {α : A →ₗ[R] A'} {β : B →ₗ[R] B'} {γ : C →ₗ[R] C'} {δ : D →ₗ[R] D'}
variables (fg : f.range = g.ker) (gh : g.range = h.ker)
variables (fg' : f'.range = g'.ker) (gh' : g'.range = h'.ker)
variables (comm₁ : f'.comp α = β.comp f) (comm₂ : g'.comp β = γ.comp g) (comm₃ : h'.comp γ = δ.comp h)

include gh fg' comm₁ comm₂ comm₃

section
include fg

lemma modfour' (hα : α.range = ⊤) (hβ : β.ker = ⊥) (hδ : δ.ker = ⊥) : γ.ker = ⊥ :=
ker_eq_bot_of_mono' (up γ) $ four ((exact_is_exact (up f) (up g)).2 fg)
  ((exact_is_exact (up g) (up h)).2 gh)
  ((exact_is_exact (up f') (up g')).2 fg')
  ((exact_is_exact (up g') (up h')).2 gh')
  comm₁ comm₂ comm₃
  (epi_of_range_eq_top α hα)
  (mono_of_ker_eq_bot β hβ)
  (mono_of_ker_eq_bot δ hδ)

end


end four
