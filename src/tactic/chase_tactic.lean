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

/-- An exactness statement. -/
meta structure exactness_lemma :=
(lhs rhs : morphism_chain)
(e : expr)

/-- The morphisms and lemmas in the context. -/
meta structure chase_data :=
(morphisms : list morphism)
(comm_lemmas : list commutativity_lemma)
(elem_lemmas : list element_lemma)
(exact_lemmas : list exactness_lemma)

meta instance format_morphism : has_to_format morphism :=
{ to_format := λ m, format!"{morphism.m m}" }

meta instance format_diagram_term : has_to_format diagram_term :=
{ to_format := λ t, format!"{t.ms} {t.elem}" }

meta instance format_commutativity_lemma : has_to_format commutativity_lemma :=
{ to_format := λ l, format!"{l.lhs} ==> {l.rhs}" }

meta instance format_element_lemma : has_to_format element_lemma :=
{ to_format := λ l, format!"{l.lhs} ==> {l.rhs}" }

meta instance format_exactness_lemma : has_to_format exactness_lemma :=
{ to_format := λ l, format!"exact {l.lhs} {l.rhs}" }

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

meta def is_mono (m : morphism) : tactic bool :=
(do i_to_expr ``(mono %%(m.m)) >>= mk_instance, return tt) <|> return ff

meta def is_epi (m : morphism) : tactic bool :=
(do i_to_expr ``(epi %%(m.m)) >>= mk_instance, return tt) <|> return ff

meta def has_domain (e : expr) (m : morphism) : tactic bool :=
(do is_def_eq m.domain e, return tt) <|> return ff

meta def is_mono_with_domain (e : expr) (m : morphism) : tactic bool :=
do
  l ← has_domain e m,
  match l with
  | ff := return ff
  | tt := is_mono m
  end

meta def has_apply_domain (e : expr) (m : morphism) : tactic bool :=
(do
  u ← i_to_expr ``(coe_sort %%(tactic.chase.morphism.domain m)),
  is_def_eq u e,
  return tt) <|> return ff

meta def morphism.can_apply (e : expr) (m : morphism) : tactic bool :=
do t ← infer_type e, has_apply_domain t m

meta def morphism_chain.can_apply (e : expr) : morphism_chain → tactic bool
| [] := return false
| (m::[]) := m.can_apply e
| (m::ms) := morphism_chain.can_apply ms

meta def monos_with_domain (e : expr) : chase_tactic (list morphism) :=
do
  s ← get,
  list.mfilter (λ m, is_mono_with_domain e m) $ s.morphisms

meta def mono_with_domain (e : expr) : chase_tactic (option morphism) :=
monos_with_domain e >>= (return ∘ list.head')

meta def epis (e : list morphism) : tactic (list morphism) :=
list.mfilter is_epi e

/-- Try to parse `e` as a morphism. -/
meta def as_morphism (e : expr) : tactic (option morphism) :=
do
  `(%%l ⟶ %%r) ← infer_type e | return none,
  trace "A",
  trace e,
  app ← mk_app `coe_fn [e],
  trace "A'",
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
  trace "B",
  expr.app `(coe_fn %%f) `(%%x) ← return e | return $ some ⟨[], e⟩,
  trace "B'",
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

/-- Try to parse `e` as an exactness lemma. -/
meta def as_exactness_lemma (e : expr) : tactic (option exactness_lemma) :=
do
  `(category_theory.abelian.exact %%f %%g) ← infer_type e | return none,
  some lhs ← as_morphism_chain f | return none,
  some rhs ← as_morphism_chain g | return none,
  return $ some ⟨lhs, rhs, e⟩

meta def epis_as_exact (e : list morphism) : tactic (list exactness_lemma) :=
epis e >>= (list.mmap $ λ m,
do
  ep ← i_to_expr ``(epi %%(m.m)) >>= mk_instance,
  a ← mk_app `category_theory.abelian.exact_zero_of_epi' [ep],
  some l ← as_exactness_lemma a,
  return l)

meta def exactness_lemmas_for (m : morphism_chain) : chase_tactic (list exactness_lemma) :=
do
  l ← get,
  return $ list.filter (λ lem, to_bool $ exactness_lemma.lhs lem = m) l.exact_lemmas

meta def get_morphisms : tactic (list morphism) :=
local_context >>= list.mfiltermap as_morphism

meta def get_comm_lemmas : tactic (list commutativity_lemma) :=
local_context >>= list.mfiltermap as_commutativity_lemma

meta def get_elem_lemmas : tactic (list element_lemma) :=
local_context >>= list.mfiltermap as_element_lemma

meta def get_exact_lemmas : tactic (list exactness_lemma) :=
local_context >>= list.mfiltermap as_exactness_lemma

meta def get_exact_lemmas_with_epi (ms : list morphism) : tactic (list exactness_lemma) :=
do
  found ← get_exact_lemmas,
  ep ← epis_as_exact ms,
  return $ list.append found ep

meta def exact_lemma_to_comm_lemmas (e : exactness_lemma) : tactic (list commutativity_lemma) :=
do
  some fi ← i_to_expr ``((%%e.e).1) >>= as_commutativity_lemma,
  some se ← i_to_expr ``((%%e.e).2) >>= as_commutativity_lemma,
  return [fi, se]

meta def exact_lemmas_to_comm_lemmas (e : list exactness_lemma) : tactic (list commutativity_lemma) :=
do
  l ← list.mmap exact_lemma_to_comm_lemmas e,
  return $ list.join l

meta def mk_chase_data : tactic chase_data :=
do
  ms ← get_morphisms,
  cs ← get_comm_lemmas,
  es ← get_elem_lemmas,
  ess ← list.mmap element_lemma.symm es,
  exs ← get_exact_lemmas_with_epi ms,
  ecs ← exact_lemmas_to_comm_lemmas exs,
  let cs' := list.append cs ecs,
  css ← list.mmap commutativity_lemma.symm cs',
  return ⟨ms, list.append cs' css, list.append es ess, exs⟩

meta def run_chase_tactic_with_data {α} (t : chase_tactic α) (d : chase_data) : tactic α :=
do
  (res, _) ← t.run d,
  return res

meta def run_chase_tactic {α} (t : chase_tactic α) : tactic α :=
mk_chase_data >>= run_chase_tactic_with_data t

meta def add_elem_lemma (l : element_lemma) : chase_tactic unit :=
do
  ⟨ms, cs, es, el⟩ ← get,
  ls ← l.symm,
  put ⟨ms, cs, (ls::l::es), el⟩

end tactic.chase
