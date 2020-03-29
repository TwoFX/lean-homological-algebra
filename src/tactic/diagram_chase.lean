/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import pseudoelements
import tactic.combinators
import tactic.chase_tactic
import tactic.commutativity

open category_theory
open category_theory.abelian
open category_theory.abelian.pseudoelements
open tactic

namespace tactic.chase

meta def pushforward_single (e : expr) (m : morphism) (n : name) : chase_tactic expr :=
do
  cr ← pose n none (expr.app m.app e),
  hyp_name ← get_unused_name ("h" ++ n),
  ty ← i_to_expr ``(%%(expr.app m.app e) = %%cr),
  x ← mk_eq_refl cr,
  hyp ← assertv hyp_name ty x,
  some l ← as_element_lemma hyp,
  add_elem_lemma l,
  return cr

meta def pushforward : expr → morphism_chain → name → chase_tactic (option expr)
| _ [] _ := return none
| e (m::[]) n := some <$> pushforward_single e m n
| e (m::ms) n := do
  nn ← mk_fresh_name,
  some f ← pushforward e ms nn,
  some <$> pushforward_single f m n

meta def pullback (e : expr) (m : morphism_chain) (n : name) : chase_tactic (option expr) :=
do
exactness_lemmas_for m >>= list.mfoldl (λ r l,
  match r with
  | some r := return $ some r
  | none := do
    z ← diagram_term.zero ⟨l.rhs, e⟩,
    cond ← find_proof ⟨l.rhs, e⟩ z,
    match cond with
    | none := return none
    | some p := do
      s ← i_to_expr ``(exists.elim ((pseudo_exact_of_exact %%l.e).2 %%e %%p)),
      tactic.apply s,
      f ← tactic.intro n,
      hyp_name ← get_unused_name ("h" ++ n),
      hyp ← tactic.intro hyp_name,
      some hy ← as_element_lemma hyp,
      add_elem_lemma hy,
      return f
    end
  end) none

meta def chase : expr → list morphism_chain → list name → chase_tactic unit
| e [] _ := skip
| e (m::ms) [] := do n ← get_unused_name "x", chase e (m::ms) [n]
| e (m::ms) (n::ns) :=
  do
    ca ← morphism_chain.can_apply e m,
    some ne ← if ca then pushforward e m n else pullback e m n,
    chase ne ms ns

end tactic.chase

namespace tactic.interactive

open interactive (parse)
open lean.parser (tk)
open interactive.types (texpr with_ident_list pexpr_list)

meta def chase (s : parse lean.parser.pexpr) (maps : parse (tk "using" *> pexpr_list))
  (ids : parse with_ident_list) : tactic unit :=
do
  e ← i_to_expr s,
  mps ← list.mmap
    (λ p, do q ← i_to_expr p, some ch ← tactic.chase.as_morphism_chain q, return ch) maps,
  tactic.chase.run_chase_tactic $ tactic.chase.chase e mps ids

end tactic.interactive
