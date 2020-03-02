import data.list
import tactic.tidy
import linear_algebra

namespace tactic

meta def rb (e : Prop) [decidable e] : tactic bool :=
if e then return tt else return ff

/-- Returns "functions" in the local context to which a can be applied.
    This is terrible. There has to be a better way to do this. -/
meta def can_apply (a : expr) : tactic (list expr) :=
local_context >>= list.mfilter (λ f, (do
  b ← i_to_expr_strict ``(%%f %%a),
  return tt) <|> return ff)

meta def domain (f : expr) : tactic expr :=
do
  `(%%X → %%Y) ← infer_type f,
  return X

meta def codomain (f : expr) : tactic expr :=
do
  `(%%X → %%Y) ← infer_type f,
  return Y

meta def eqs_with_domain (A : expr) : tactic (list expr) :=
local_context >>= list.mfilter (λ e, do
  `(%%l = %%r) ← infer_type e | return ff,
  `(%%X → %%Y) ← infer_type l | return ff,
  rb (X = A))

meta def introduce_map (f : expr) : tactic unit :=
do
  n ← get_unused_name "h",
  tactic.interactive.«have» n none ``(linear_map.map_zero %%f)

meta def introduce_hypothesis (h : expr) : tactic unit :=
do
  `(%%l = %%r) ← infer_type h,
  funs ← can_apply l,
  list.mmap' (λ f, do
    n ← get_unused_name "h",
    tactic.interactive.«have» n ``(%%f %%l = %%f %%r) ``(congr_arg %%f %%h)) funs

/-- Generates local hypotheses for all commutativity lemmas that apply to `a`. -/
meta def introduce_element (a : expr) : tactic unit :=
do
  A ← infer_type a,
  es ← eqs_with_domain A,
  list.mmap' (λ e, do
    n ← get_unused_name "h",
    tactic.interactive.«have» n none ``(congr_fun %%e %%a)) es,
  tactic.interactive.simp none tt [simp_arg_type.expr ``(function.comp_apply)] [] interactive.loc.wildcard <|> skip,
  skip

meta def find_first {α : Sort*} (m : α → tactic bool) (l : list α) : tactic (option α) :=
do
  a ← list.mfilter m l,
  match a with
  | [] := return none
  | (h :: hs) := return (some h)
  end

meta def find_uni (f : pexpr) : tactic (option expr) :=
do
  ctx ←local_context,
  U ← i_to_expr_no_subgoals f,
  find_first (λ e, (do
    T ← infer_type e,
    unify T U,
    return tt) <|> return ff) ctx

meta def find_exact (f : expr) : tactic (option expr) :=
do
  ctx ←local_context,
  find_first (λ e, (do
    `(linear_map.range %%h = linear_map.ker %%g) ← infer_type e,
    unify f h,
    return tt) <|> return ff) ctx

meta def get_tk (e : expr) : tactic expr :=
do
  `(linear_map.range %%f = linear_map.ker %%g) ← infer_type e,
  return g

meta def injective_apply : tactic unit :=
do
  g::gs ← get_goals,
  `(%%l = %%r) ← infer_type g,
  A ← infer_type l,
  funs ← can_apply l,
  inj_funs ← list.mmap (λ f, do i ← find_uni ``(function.injective %%f), return (f, i)) funs,
  inj_funs' ← list.mfilter (λ (h : expr × (option expr)),
    match h with
    | (_, none) := return ff
    | _ := return tt
    end) inj_funs,
  match inj_funs' with
  | ((a, some b) :: fs) := apply b >> skip
  | _ := skip
  end

/-- Solves the top goal by commutativity -/
meta def comm_dispatch : tactic unit :=
injective_apply >> tactic.cc

/-- Proves `g` by commutativity and introduces the hypothesis `n : g` -/
meta def comm_solve (n : name) (g : pexpr) : tactic unit :=
do
  tactic.interactive.«have» n g none,
  g::gs ← get_goals,
  set_goals [g],
  comm_dispatch,
  done,
  set_goals gs

meta def pushforward (t : expr) (f' : pexpr) (mid : name) : tactic (expr × expr) :=
do
  tactic.interactive.«let» mid none ``(%%f' %%t),
  q ← get_local mid,
  n ← get_unused_name "h",
  tactic.interactive.«have» n ``(%%f' %%t = %%q) ``(rfl),
  r ← get_local n,
  return (q, r)

meta def pullback (t : expr) (f' : pexpr) (mid : name) : tactic (expr × expr) :=
do
  f ← i_to_expr f',
  s' ← find_uni ``(function.surjective %%f),
  match s' with
  | some s := do
    i_to_expr ``(exists.elim (%%s %%t)) >>= apply,
    c ← tactic.intro mid,
    n ← get_unused_name "h",
    d ← tactic.intro n,
    return (c, d)
  | none := do
    h' ← find_exact f,
    match h' with
    | some h := do
      p ← get_tk h,
      n ← get_unused_name "h",
      comm_solve n ``(%%p %%t = 0),
      hn ← get_local n,
      m ← get_unused_name "h",
      tactic.interactive.«have» m none ``(linear_map.mem_ker.2 %%hn),
      hm ← get_local m,
      o ← get_unused_name "h",
      tactic.interactive.«have» o ``(%%t ∈ linear_map.range %%f) ``((%%h).symm ▸ %%hm),
      ho ← get_local o,
      i_to_expr ``(exists.elim %%ho) >>= apply,
      c ← tactic.intro mid,
      z ← mk_fresh_name,
      d ← tactic.intro z,
      i_to_expr ``(and.elim %%d) >>= apply,
      z1 ← mk_fresh_name,
      z2 ← get_unused_name "h",
      tactic.intro z1,
      d ← tactic.intro z2,
      return (c, d)
    | none := tactic.fail "Cannot chase along this function"
    end
  end

--meta def chase (s : pexpr) (hyps : list pexpr) (maps : list pexpr) (ids : list name)
--  (fin : pexpr) : tactic unit :=
meta def chase : pexpr → list pexpr → list pexpr → list name → pexpr → tactic unit :=
λ s hyps maps ids fin,
do
  t ← i_to_expr s,
  introduce_element t,
  hyps.mmap' (λ h', do h ← i_to_expr_strict h', introduce_hypothesis h),
  match maps with
  | [] := do
    n ← get_unused_name "h",
    comm_solve n fin
  | (f' :: fs) := do
    f ← i_to_expr ``((%%f').to_fun),
    dom ← domain f,
    cod ← codomain f,
    t' ← infer_type t,
    ite (dom = t') (do
      (q, r) ← pushforward t f' ids.head,
      chase (pexpr.of_expr q) [(pexpr.of_expr r)] fs ids.tail fin
    ) $
    ite (cod = t') (do
      (c, d) ← pullback t f' ids.head, 
      chase (pexpr.of_expr c) [(pexpr.of_expr d)] fs ids.tail fin) $
    tactic.fail "Cannot chase along this function"
  end

namespace interactive

open interactive (parse)
open lean.parser (tk)
open interactive.types (texpr with_ident_list pexpr_list)

/- dc [←g, β, ←f', ←α] with b a' a using λ (b : B) (a' : A') (a : A), f b = a -/
meta def chase (s : parse lean.parser.pexpr) (hyps : parse pexpr_list) (maps : parse (tk "using" *> pexpr_list))
  (ids : parse with_ident_list) (fin : parse (tk "only" *> texpr)) : tactic unit :=
tactic.chase s hyps maps ids fin

end interactive
end tactic