import data.list

namespace tactic

/-- Returns a proof of `cur = goal` by concatenating local hypotheses -/
meta def transitivity_dfs : expr → expr → list expr → tactic (option expr) :=
λ cur goal seen,
ite (cur = goal) (some <$> mk_eq_refl cur) $
local_context >>= list.mfoldl (λ (s : option expr) (f : expr), do
  match s with
  | some s := return (some s)
  | none := (do

    let recurse : expr → expr → tactic (option expr) := (λ ne eq,
      ite (list.any seen (λ e, if e = ne then tt else ff)) (return none) $ do
      r ← transitivity_dfs ne goal (ne::seen),
      match r with
      | none := return none
      | some p := some <$> mk_eq_trans eq p
      end),

    `(%%l = %%r) ← infer_type f,
    
    fi ← ite (l = cur) (recurse r f) (return none),
    
    match fi with
    | some p := return p
    | none := ite (r = cur) (mk_eq_symm f >>= recurse l) (return none)
    end) <|> return none
  end) none

meta def transitivity' : tactic unit := do
  `(%%l = %%r) ← target,
  op ← transitivity_dfs l r [],
  match op with
  | some p := tactic.exact p
  | none := tactic.fail "Unable to prove equality from local hypotheses"
  end

namespace interactive

meta def transitivity' : tactic unit :=
tactic.transitivity'

end interactive

end tactic