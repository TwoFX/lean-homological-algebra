import category_theory.limits.shapes.terminal category_theory.limits.shapes.equalizers

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_initial.{v} C]
include 𝒞

class has_zero_object :=
(terminal_eq_initial' : (⊤_ C) = ⊥_ C . obviously)

restate_axiom has_zero_object.terminal_eq_initial'

abbreviation zero [has_zero_object.{v} C] : C := ⊤_ C

notation `_0` C:60 := zero C
--instance [has_zero_object.{v} C] : has_zero C := ⟨⊤_ C⟩

section
variables {C} [has_zero_object.{v} C]

lemma zero.eq_terminal : _0 C = ⊤_ C := rfl

lemma zero.eq_initial : _0 C = ⊥_ C :=
by rw [zero.eq_terminal, has_zero_object.terminal_eq_initial.{v} C]

abbreviation zero.from  (P : C) : P ⟶ _0 C := terminal.from P

abbreviation zero.to (P : C) : _0 C ⟶ P :=
by { rw zero.eq_initial, exact initial.to P }

instance unique_to_zero (P : C) : unique (P ⟶ _0 C) :=
limits.unique_to_terminal P

instance unique_from_zero (P : C) : unique (_0 C ⟶ P) :=
by { rw zero.eq_initial, exact limits.unique_from_initial P }

abbreviation zero_mor (P : C) (Q : C) : P ⟶ Q :=
(zero.from P) ≫ (zero.to Q)

instance {P Q : C} : has_zero (P ⟶ Q) := ⟨zero_mor P Q⟩

lemma zero.from_zero {P : C} (f : _0 C ⟶ P) : f = 0 :=
by rw [(limits.unique_from_zero P).uniq f, (limits.unique_from_zero P).uniq 0]

lemma zero.to_zero {P : C} (f : P ⟶ _0 C) : f = 0 :=
by rw [(limits.unique_to_zero P).uniq f, (limits.unique_to_zero P).uniq 0]

/- Borceux 2, Prop. 1.1.4 -/
lemma zero_comp (P : C) {Q R : C} (g : Q ⟶ R) : (0 : P ⟶ Q) ≫ g = 0 :=
begin
  unfold has_zero.zero,
  delta zero_mor,
  rw [category.assoc', zero.from_zero (zero.to Q ≫ g), zero.from_zero (zero.to R)]
end

/- Borceux 2, Prop. 1.1.4 -/
lemma comp_zero {P Q : C} (R : C) (f : P ⟶ Q) : f ≫ (0 : Q ⟶ R) = 0 :=
begin
  unfold has_zero.zero,
  delta zero_mor,
  rw [←category.assoc', zero.to_zero (f ≫ zero.from Q), zero.to_zero (zero.from P)]
end

/- Borceux 2, Prop 1.1.6 -/
lemma zero_comp' {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} [mono g] (h : f ≫ g = 0) : f = 0 :=
by { rw [←zero_comp P g, cancel_mono g] at h, exact h }

end 
end category_theory.limits