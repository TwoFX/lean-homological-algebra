import data.list
import tactic.tidy
import linear_algebra
import transitivity

section
variables {R : Type*} [ring R]
variables {A : Type*} {B : Type*} {C : Type*}
variables [add_comm_group A] [add_comm_group B] [add_comm_group C]
variables [module R A] [module R B] [module R C]
variables {f : A →ₗ[R] B} {g : B →ₗ[R] C} 

lemma exact_apply (fg : linear_map.range f = linear_map.ker g) (a : A) : g (f a) = 0 :=
linear_map.mem_ker.1 $ fg ▸ submodule.mem_map_of_mem trivial

end

namespace tactic

meta def rb (e : Prop) [decidable e] : tactic bool :=
if e then return tt else return ff

meta def resolve : tactic unit :=
tactic.transitivity'

meta def cad := list (expr × expr)

meta def can_apply_data : tactic cad :=
local_context >>= list.mfoldl (λ (s : list (expr × expr)) (f : expr), (do
    b ← mk_app `coe_fn [f],
    return ((b, f)::s)
    ) <|> return s) []

/-- Returns "functions" in the local context to which a can be applied.
    This is terrible. There has to be a better way to do this. -/
meta def can_apply (a : expr) (c : cad) : tactic (list expr) :=
list.mfoldl (λ (s : list expr) (d : expr × expr),  (do
  match d with (b, f) := do
    T ← infer_type b,
    u ← mk_mvar,
    v ← mk_mvar,
    e ← i_to_expr ``(%%u → %%v),
    unify T e,
    U ← infer_type a,
    unify u U,
    return (f::s)
  end) <|> return s) [] c

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

meta def introduce_hypothesis (h : expr) (c : cad) : tactic unit :=
do
  `(%%l = %%r) ← infer_type h,
  funs ← can_apply l c,
  list.mmap' (λ f, do
    n ← get_unused_name "h",
    tactic.interactive.«have» n ``(%%f %%l = %%f %%r) ``(congr_arg %%f %%h)) funs
  

meta def introduce_map (c : cad) (f : expr) : tactic unit :=
(do
  n ← get_unused_name "h",
  tactic.interactive.«have» n none ``(linear_map.map_zero %%f),
  h ← get_local n,
  introduce_hypothesis h c) <|> skip

meta def introduce_maps (c : cad) : tactic unit :=
local_context >>= list.mmap' (introduce_map c)

/-- Generates local hypotheses for all commutativity lemmas that apply to `a`. -/
meta def introduce_element (a : expr) : tactic unit :=
do
  A ← infer_type a,
  es ← eqs_with_domain A,
  list.mmap' (λ e, do
    n ← get_unused_name "h",
    tactic.interactive.«have» n none ``(congr_fun %%e %%a)) es,
  tactic.interactive.simp none tt [simp_arg_type.expr ``(function.comp_apply)] [] interactive.loc.wildcard <|> skip,
  ctx ← local_context,
  list.mmap' (λ f, (do
    n ← get_unused_name "h",
    `(linear_map.range %%h = linear_map.ker %%g) ← infer_type f,
    b ← mk_app `exact_apply [f, a],
    c ← i_to_expr ``(%%g (%%h %%a) = 0),
    tactic.assertv n c b,
    skip) <|> skip) ctx,
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

meta def find_injective (f : expr) : tactic (option expr) :=
do
  i ← find_uni ``(function.injective %%f),
  match i with
  | some e := return (some e)
  | none := do
    k ← find_uni ``(linear_map.ker %%f = ⊥),
    match k with
    | some e := do
      n ← get_unused_name "h",
      inj ← i_to_expr_strict ``(function.injective (coe_fn %%f)),
      --ap ← mk_app `linear_map.ker_eq_bot.mp [f], TODO: Why does this not work?
      ap ← i_to_expr ``(linear_map.ker_eq_bot.1 %%e),
      r ← tactic.assertv n inj ap,
      return (some r)
    | none := return none
    end
  end

meta def find_surjective (f : expr) : tactic (option expr) :=
do
  i ← find_uni ``(function.surjective %%f),
  match i with
  | some e := return (some e)
  | none := do
    k ← find_uni ``(linear_map.range %%f = ⊤),
    match k with
    | some e := do
      n ← get_unused_name "h",
      sur ← i_to_expr_strict ``(function.surjective (coe_fn %%f)),
      ap ← i_to_expr ``(linear_map.range_eq_top.1 %%e),
      r ← tactic.assertv n sur ap,
      return (some r)
    | none := return none
    end
  end

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

meta def injective_apply (c : cad) : tactic unit :=
do
  g::gs ← get_goals,
  `(%%l = %%r) ← infer_type g,
  A ← infer_type l,
  funs ← can_apply l c,
  inj_funs ← list.mmap (λ f, do i ← find_injective f, return (f, i)) funs,
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
meta def comm_dispatch (c : cad) : tactic unit :=
injective_apply c >> injective_apply c >> resolve

/-- Proves `g` by commutativity and introduces the hypothesis `n : g` -/
meta def comm_solve (n : name) (g : pexpr) (c : cad) : tactic unit :=
do
  tactic.interactive.«have» n g none,
  g::gs ← get_goals,
  set_goals [g],
  comm_dispatch c,
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

meta def pullback (t : expr) (f' : pexpr) (mid : name) (c : cad) : tactic (expr × expr) :=
do
  f ← i_to_expr f',
  s' ← find_surjective f,
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
      comm_solve n ``(%%p %%t = 0) c,
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

meta def chase (c : cad) : pexpr → list pexpr → list pexpr → list name → pexpr → tactic unit :=
λ s hyps maps ids fin,
do
  t ← i_to_expr s,
  introduce_element t,
  --hyps.mmap' (λ h, introduce_hypothesis <$> i_to_expr_strict h),
  hyps.mmap' (λ h', do h ← i_to_expr_strict h', introduce_hypothesis h c),
  match maps with
  | [] := do
    n ← get_unused_name "h",
    comm_solve n fin c,
    h ← get_local n,
    introduce_hypothesis h c
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
      (c, d) ← pullback t f' ids.head c, 
      chase (pexpr.of_expr c) [(pexpr.of_expr d)] fs ids.tail fin) $
    tactic.fail "Cannot chase along this function"
  end

namespace interactive

open interactive (parse)
open lean.parser (tk)
open interactive.types (texpr with_ident_list pexpr_list)

/- dc [←g, β, ←f', ←α] with b a' a using λ (b : B) (a' : A') (a : A), f b = a -/
meta def chase' (s : parse lean.parser.pexpr) (hyps : parse pexpr_list) (maps : parse (tk "using" *> pexpr_list))
  (ids : parse with_ident_list) (fin : parse (tk "only" *> texpr)) : tactic unit := do
c ← can_apply_data,
tactic.introduce_maps c >> tactic.chase c s hyps maps ids fin

meta def chase (s : parse lean.parser.pexpr) (hyps : parse pexpr_list) (maps : parse (tk "using" *> pexpr_list))
  (ids : parse with_ident_list) (fin : parse (tk "only" *> texpr)) : tactic unit := do
c ← can_apply_data,
tactic.introduce_maps c >> tactic.chase c s hyps maps ids fin >> comm_dispatch c

end interactive
end tactic