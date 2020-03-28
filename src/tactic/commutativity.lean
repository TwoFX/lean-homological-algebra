/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import category_theory.category
import pseudoelements
import tactic.combinators
import tactic.chase_tactic

open category_theory
open category_theory.abelian
open category_theory.abelian.pseudoelements
open tactic

namespace tactic.chase

section lemmas
universes v u
variables {C : Type u} [𝒞 : category.{v} C] [abelian.{v} C]
include 𝒞

local attribute [instance] object_to_sort
local attribute [instance] hom_to_fun

lemma pseudo_congr {X Y : C} {f g : X ⟶ Y} (h : f = g) (x : X) : f x = g x :=
by rw h

end lemmas

meta def try_apply_comm_lemma_at_aux (l : commutativity_lemma) :
  ℕ → diagram_term → option (diagram_term)
| 0 ⟨ms, elem⟩ :=
  match list.is_prefix_of l.lhs ms with
  | ff := none
  | tt := some ⟨list.append l.rhs (list.drop l.lhs.length ms), elem⟩
  end
| (n + 1) ⟨[], e⟩ := none
| (n + 1) ⟨t::ts, e⟩ :=
  match try_apply_comm_lemma_at_aux n ⟨ts, e⟩ with
  | none := none
  | some ⟨nt, ne⟩ := some ⟨t::nt, ne⟩
  end

meta def try_apply_element_lemma_at_aux (l : element_lemma) :
  ℕ → diagram_term → option (diagram_term)
| 0 ⟨ms, elem⟩ := if l.lhs = ⟨ms, elem⟩ then some l.rhs else none
| (n + 1) ⟨[], e⟩ := none
| (n + 1) ⟨t :: ts, e⟩ :=
  match try_apply_element_lemma_at_aux n ⟨ts, e⟩ with
  | none := none
  | some ⟨nt, ne⟩ := some ⟨t::nt, ne⟩
  end

meta inductive lemma_app
| comm : commutativity_lemma → ℕ → diagram_term → lemma_app
| elem : element_lemma → ℕ → diagram_term → lemma_app

meta instance format_lemma_app : has_to_format lemma_app :=
{ to_format := λ a,
  match a with
  | lemma_app.comm a b c := format!"comm: lemma ({a}) at {b} gives {c}"
  | lemma_app.elem a b c := format!"elem: lemma ({a}) at {b} gives {c}"
  end }

meta def next_term : lemma_app → diagram_term
| (lemma_app.comm _ _ t) := t
| (lemma_app.elem _ _ t) := t

meta def apply_comm_lemma_at_aux : ℕ → diagram_term → tactic (option expr)
| 0 t := some <$> (mk_eq_refl $ as_expr t)
| (n + 1) ⟨[], _⟩ := none
| (n + 1) ⟨t::[], e⟩ := none
| (n + 1) ⟨t::(u::ts), e⟩ :=
do
  some x ← i_to_expr ``(%%(u.m) ≫ %%(t.m)) >>= as_morphism,
  lhs ← mk_app `category_theory.abelian.pseudoelements.comp_apply [u.m, t.m, as_expr ⟨ts, e⟩] >>= mk_eq_symm,
  some rhs ← apply_comm_lemma_at_aux (n - 1) ⟨x::ts, e⟩,
  some <$> mk_eq_trans lhs rhs

meta def apply_comm_lemma_at (l : commutativity_lemma) :
  ℕ → diagram_term → diagram_term → tactic (option expr)
| 0 ⟨ms, elem⟩ goal :=
do
  some one ← apply_comm_lemma_at_aux (l.lhs.length) ⟨ms, elem⟩,
  let inner := as_expr ⟨list.drop (l.lhs.length) ms, elem⟩,
  two ← mk_app `tactic.chase.pseudo_congr [l.e, inner],
  some three ← apply_comm_lemma_at_aux (l.lhs.length) goal,
  three' ← mk_eq_symm three,
  onetwo ← mk_eq_trans one two,
  some <$> mk_eq_trans onetwo three'
| (n + 1) ⟨[], e⟩ goal := none
| (n + 1) fr ⟨[], e⟩ := none
| (n + 1) ⟨t::ts, e⟩ ⟨u::us, f⟩ :=
do
  some inner ← apply_comm_lemma_at n ⟨ts, e⟩ ⟨us, f⟩,
  some <$> mk_app `congr_arg [t.app, inner]

meta def apply_elem_lemma_at (l : element_lemma) :
  ℕ → diagram_term → tactic (option expr)
| 0 ⟨ms, elem⟩ := return $ some l.e
| (n + 1) ⟨[], _⟩ := none
| (n + 1) ⟨t::ts, e⟩ :=
do
  some inner ← apply_elem_lemma_at n ⟨ts, e⟩,
  some <$> mk_app `congr_arg [t.app, inner]

meta def build_proof (t : diagram_term) : lemma_app → tactic expr
| (lemma_app.comm x y z) :=
do
  some u ← apply_comm_lemma_at x y t z,
  return u
| (lemma_app.elem x y z) :=
do
  some u ← apply_elem_lemma_at x y t,
  return u

meta def try_apply_comm_lemma_at (l : commutativity_lemma) (n : ℕ) (t : diagram_term) :
  option (lemma_app) :=
match try_apply_comm_lemma_at_aux l n t with
| none := none
| some t := lemma_app.comm l n t
end

meta def try_apply_elem_lemma_at (l : element_lemma) (n : ℕ) (t : diagram_term) :
  option lemma_app :=
match try_apply_element_lemma_at_aux l n t with
| none := none
| some t := lemma_app.elem l n t
end

meta def iota : ℕ → list ℕ
| 0 := [0]
| (n + 1) := (n + 1) :: iota n

meta def try_apply_comm_lemma (l : commutativity_lemma) (t : diagram_term) : list lemma_app :=
list.filter_map (λ n, try_apply_comm_lemma_at l n t) $ iota t.ms.length

meta def try_apply_elem_lemma (l : element_lemma) (t : diagram_term) : list lemma_app :=
list.filter_map (λ n, try_apply_elem_lemma_at l n t) $ iota t.ms.length

meta def try_all_comm (t : diagram_term) : chase_tactic (list lemma_app) :=
do
  ⟨ms, cs, es⟩ ← get,
  return $ list.join $ list.map (λ l, try_apply_comm_lemma l t) cs

meta def try_all_elem (t : diagram_term) : chase_tactic (list lemma_app) :=
do
  ⟨ms, cs, es⟩ ← get,
  return $ list.join $ list.map (λ l, try_apply_elem_lemma l t) es

meta mutual def show_via_zero, find_proof_dfs
with show_via_zero : diagram_term → diagram_term → chase_tactic (option expr)
| cur goal := do
  l ← diagram_term.to_zero cur,
  match l with
  | none := return none
  | some e := do
    zer ← goal.zero,
    r ← find_proof_dfs goal zer [],
    match r with
    | none := return none
    | some f := (mk_eq_symm f) >>= (λ g, some <$> mk_eq_trans e g)
    end
  end
with find_proof_dfs :
diagram_term → diagram_term → list diagram_term → chase_tactic (option expr)
| cur goal seen := if cur = goal then some <$> mk_eq_refl (as_expr cur) else
do
  via_zero ← show_via_zero cur goal,
  match via_zero with
  | some e := return $ some e
  | none := do
    cands_comm ← try_all_comm cur,
    cands_elem ← try_all_elem cur,
    let cands := list.append cands_comm cands_elem,

    list.mfoldl (λ r s,
      match r with
      | some q := return $ some q
      | none :=
        ite (list.any seen (λ e, to_bool $ e = (next_term s))) (return none) $
        do
          --trace format!"trying {s}...",
          l ← find_proof_dfs (next_term s) goal (cur::seen),
          match l with
          | none := none
          | some q := do
            f ← build_proof cur s,
            t ← mk_eq_trans f q,
            return $ some t
          end
      end) none cands
    end

meta def find_proof (cur goal : diagram_term) : chase_tactic (option expr) :=
find_proof_dfs cur goal []

meta def commutativity : chase_tactic unit :=
do
  (_, l, r) ← target_lhs_rhs,
  some lhs ← as_diagram_term l,
  some rhs ← as_diagram_term r,
  some p ← find_proof lhs rhs,
  tactic.exact p

end tactic.chase

namespace tactic.interactive

open interactive (parse)

meta def to_zero (s : parse lean.parser.pexpr) : tactic unit :=
do
  u ← i_to_expr s,
  some m ← tactic.chase.as_diagram_term u,
  some e ← tactic.chase.diagram_term.to_zero m,
  tactic.exact e

meta def commutativity : tactic unit :=
chase.run_chase_tactic tactic.chase.commutativity

end tactic.interactive
