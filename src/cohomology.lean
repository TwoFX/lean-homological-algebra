import abelian
import exact

open category_theory
open category_theory.limits

universes v u

namespace category_theory.abelian

section
variables (A : Type u) [𝒜 : category.{v} A] [abelian.{v} A]
include 𝒜

structure cochain_complex :=
(mod : Π (n : ℤ), A)
(c : Π (n : ℤ), mod n ⟶ mod (n + 1))
(condition : ∀ (n : ℤ), (c n) ≫ (c (n + 1)) = 0)

def cohomology (C : cochain_complex.{v} A) (n : ℤ) : A :=
let m := n - 1 in
cokernel (kernel.lift (C.c (m + 1)) (C.c m) (C.condition _) )



end

end category_theory.abelian