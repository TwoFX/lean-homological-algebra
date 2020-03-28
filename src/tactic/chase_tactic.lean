/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.category
import pseudoelements
import tactic.combinators

open category_theory
open category_theory.abelian
open tactic

namespace tactic.chase

/-- A morphism in an abelian category. -/
@[derive decidable_eq]
meta structure morphism :=
(m : expr)
(domain : expr)
(codomain : expr)
(app : expr)

/-- A sequence of morphisms in an abelian category, in "mathematical order":
    `[f₁, ..., fₙ]` represents `fₙ ≫ ... ≫ f₁`. -/
@[reducible]
meta def morphism_chain := list morphism

/-- An expression of the form `f₁ (f₂ (... (fₙ a)))`, with `a` a pseudoelement. -/
@[derive decidable_eq]
meta structure diagram_term :=
(ms : morphism_chain)
(elem : expr)

/-- A commutativity lemma in a category. -/
meta structure commutativity_lemma :=
(lhs rhs : morphism_chain)
(e : expr)

/-- A lemma of the form `f₁ (f₂ (... (fₙ a))) = g₁ (g₂ (... (gₘ a)))`, with `a` a pseudoelement. -/
meta structure element_lemma :=
(lhs rhs : diagram_term)
(e : expr)

/-- The morphisms and lemmas in the context. -/
meta structure chase_data :=
(morphisms : list morphism)
(comm_lemmas : list commutativity_lemma)
(elem_lemmas : list element_lemma)

meta instance format_morphism : has_to_format morphism :=
{ to_format := λ m, format!"{morphism.m m}" }

meta instance format_diagram_term : has_to_format diagram_term :=
{ to_format := λ t, format!"{t.ms} {t.elem}" }

meta instance format_commutativity_lemma : has_to_format commutativity_lemma :=
{ to_format := λ l, format!"{l.lhs} ==> {l.rhs}" }

meta instance format_element_lemma : has_to_format element_lemma :=
{ to_format := λ l, format!"{l.lhs} ==> {l.rhs}" }

/-- A tactic that makes use of the precomputed content of the context. -/
@[reducible]
meta def chase_tactic :=
state_t chase_data tactic

meta instance {α} : has_coe (tactic α) (chase_tactic α) :=
⟨monad_lift⟩

meta def as_expr : diagram_term → expr
| ⟨[], e⟩ := e
| ⟨t::ts, e⟩ := expr.app t.app $ as_expr ⟨ts, e⟩

meta def commutativity_lemma.symm : commutativity_lemma → tactic commutativity_lemma
| ⟨lhs, rhs, e⟩ := mk_eq_symm e >>= λ f, return ⟨rhs, lhs, f⟩

meta def element_lemma.symm : element_lemma → tactic element_lemma
| ⟨lhs, rhs, e⟩ := mk_eq_symm e >>= λ f, return ⟨rhs, lhs, f⟩

meta def morphism.is_zero (m : morphism) : tactic bool :=
do
  d ← infer_type m.m,
  z ← i_to_expr ``(0 : %%d),

  -- Why does the following not work?
  -- z ← mk_app `has_zero.zero [d],

  (do is_def_eq m.m z,
  return tt) <|> return ff

meta def diagram_term.type : diagram_term → tactic expr
| ⟨[], e⟩ := infer_type e
| ⟨t::ts, e⟩ := return t.codomain

meta def diagram_term.zero (t : diagram_term) : tactic diagram_term :=
do
  s ← t.type,
  x ← i_to_expr ``(0 : %%s),
  return ⟨[], x⟩

/-- Try to generate a proof of `as_expr t = 0`. -/
meta def diagram_term.to_zero : diagram_term → tactic (option expr)
| ⟨[], e⟩ := (do
  d ← infer_type e,
  f ← i_to_expr ``(0 : %%d),
  is_def_eq e f,
  some <$> mk_eq_refl e) <|> return none
| ⟨t::ts, e⟩ := do
  z ← t.is_zero,
  if z then some <$> mk_app
    `category_theory.abelian.pseudoelements.zero_apply [t.codomain, as_expr ⟨ts, e⟩] else do
    inner ← diagram_term.to_zero ⟨ts, e⟩,
    match inner with
    | none := return none
    | some i := do
      fs ← mk_app `congr_arg [t.app, i],
      sn ← mk_app `category_theory.abelian.pseudoelements.apply_zero [t.m],
      some <$> mk_eq_trans fs sn
    end

/-- Try to parse `e` as a morphism. -/
meta def as_morphism (e : expr) : tactic (option morphism) :=
do
  `(%%l ⟶ %%r) ← infer_type e | return none,
  app ← mk_app `coe_fn [e],
  return $ some ⟨e, l, r, app⟩

/-- Try to parse `e` as a morphism chain. -/
meta def as_morphism_chain : expr → tactic (option morphism_chain) := λ e,
do
  self ← as_morphism e,
  match self with
  | none := return none
  | some s := do
    `(%%l ≫ %%r) ← return s.m | return (some [s]),
    some u ← as_morphism_chain r | return none,
    some r ← as_morphism l | return none,
    return $ some (list.append u [r])
  end

/-- Try to parse `e` as a commutativity lemma. -/
meta def as_commutativity_lemma (e : expr) : tactic (option commutativity_lemma) :=
do
  `(%%l = %%r) ← infer_type e | return none,
  some lhs ← as_morphism_chain l | return none,
  some rhs ← as_morphism_chain r | return none,
  return $ some ⟨lhs, rhs, e⟩

/-- Try to parse `e` as a diagram term. -/
meta def as_diagram_term : expr → tactic (option diagram_term) := λ e,
do
  `(coe_sort %%l) ← infer_type e | return none,
  expr.app `(coe_fn %%f) `(%%x) ← return e | return $ some ⟨[], e⟩,
  some dt ← as_diagram_term x,
  some F ← as_morphism f,
  return $ some ⟨(F::diagram_term.ms dt), diagram_term.elem dt⟩

/-- Try to parse `e` as an element lemma. -/
meta def as_element_lemma (e : expr) : tactic (option element_lemma) :=
do
  `(%%l = %%r) ← infer_type e | return none,
  some lhs ← as_diagram_term l | return none,
  some rhs ← as_diagram_term r | return none,
  return $ some ⟨lhs, rhs, e⟩

meta def get_morphisms : tactic (list morphism) :=
local_context >>= list.mfiltermap as_morphism

meta def get_comm_lemmas : tactic (list commutativity_lemma) :=
local_context >>= list.mfiltermap as_commutativity_lemma

meta def get_elem_lemmas : tactic (list element_lemma) :=
local_context >>= list.mfiltermap as_element_lemma

meta def mk_chase_data : tactic chase_data :=
do
  ms ← get_morphisms,
  cs ← get_comm_lemmas,
  css ← list.mmap commutativity_lemma.symm cs,
  es ← get_elem_lemmas,
  ess ← list.mmap element_lemma.symm es,
  return ⟨ms, list.append cs css, list.append es ess⟩

meta def run_chase_tactic_with_data {α} (t : chase_tactic α) (d : chase_data) : tactic α :=
do
  (res, _) ← t.run d,
  return res

meta def run_chase_tactic {α} (t : chase_tactic α) : tactic α :=
mk_chase_data >>= run_chase_tactic_with_data t

meta def add_elem_lemma (l : element_lemma) : chase_tactic unit :=
do
  ⟨ms, cs, es⟩ ← get,
  put ⟨ms, cs, l::es⟩

end tactic.chase
