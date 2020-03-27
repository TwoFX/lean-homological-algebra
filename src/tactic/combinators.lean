/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

universes u v w

def list.mfiltermap {m : Type u → Type v} [monad m] {α : Type w} {β : Type u}
  (f : α → m (option β)) : list α → m (list β)
| [] := return []
| (x::xs) := do
    y ← f x,
    r ← list.mfiltermap xs,
    match y with
    | none := return r
    | some z := return (z::r)
    end
