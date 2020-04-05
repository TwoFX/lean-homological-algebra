/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/

import abelian
import exact
import pseudoelements

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

open pseudoelements

section
variables (V : Type u) [𝒱 : category.{v} V] [abelian.{v} V]
include 𝒱

local attribute [instance] has_zero_object.has_zero

end

end category_theory.abelian
