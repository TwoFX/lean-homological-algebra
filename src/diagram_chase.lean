namespace tactic

meta def find_eq (e : expr) : list expr → tactic (list pexpr)
| [] := return []
| (H :: Hs) := (do
  --trace H,
  `(%%l = %%r) ← infer_type H,
  rest ← find_eq Hs,
  if l = e then return (to_pexpr H :: rest)
  else if r = e then return (``(eq.symm %%H) :: rest)
  else return rest) <|> find_eq Hs

meta def print_all : list pexpr → tactic unit
| [] := skip
| (H :: Hs) := do
    trace H,
    tactic.interactive.«let» none none H,
    print_all Hs

namespace interactive

open interactive (parse)
open interactive.types (texpr)

meta def find_eq (e : parse texpr) : tactic unit :=
do
  ctx ← tactic.local_context,
  p ← i_to_expr e,
  l ← tactic.find_eq p ctx,
  print_all l

meta def dc : tactic unit :=
trace "dc waves its hands about in complicated patterns over the blackboard."

end interactive
end tactic