/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import modules
import exact

universe u

open category_theory.abelian
open linear_map
open Module

variables {R : Type u} [ring R]

section
variables {X Y Z : Module R} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma exact_is_exact : exact f g ↔ f.range = g.ker :=
begin
  split,
  { intro h,
    apply le_antisymm,
    { intros x hx,
      apply mem_ker.2,
      cases mem_range.1 hx with y hy,
      rw ←hy,
      rw ←linear_map.comp_apply,
      change (f ≫ g) y = 0,
      erw h.1,
      rw zero_map_apply, },
    { intros x hx,
      have hu := h.2,
      have u : x ∈ f.range.mkq.ker,
      { 
        have : x ∈ g.ker.subtype.range,
        { rw submodule.range_subtype,
          exact hx, },
        cases mem_range.1 this with y hy,
        apply mem_ker.2,
        rw ←hy,
        rw ←linear_map.comp_apply,
        conv_lhs {
          change (category_theory.limits.kernel.ι g ≫ category_theory.limits.cokernel.π f) y},
        erw hu,
        simp [zero_map_apply],
        refl, },
        rw submodule.ker_mkq at u,
        exact u,
      }, },
  { intro h,
    split,
    { ext,
      have : f x ∈ ker g,
      { rw ←h,
        exact submodule.mem_map_of_mem trivial, },
      simp [zero_map_apply],
      apply mem_ker.1,
      exact this,
      },
    { conv_lhs { congr, change g.ker.subtype, skip, change f.range.mkq },
      ext,
      simp [zero_map_apply],
      apply (submodule.quotient.mk_eq_zero f.range).2,
      rw h,
      exact x.2, } }
end

end