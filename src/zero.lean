import category_theory.limits.shapes.terminal category_theory.limits.shapes.equalizers
import category_theory.opposites data.opposite

universes v u

open category_theory
open opposite

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_initial.{v} C]
include 𝒞

class has_zero_object :=
(terminal_eq_initial' : (⊤_ C) = ⊥_ C . obviously)

restate_axiom has_zero_object.terminal_eq_initial'

abbreviation zero [has_zero_object.{v} C] : C := ⊤_ C

notation `_0` C:60 := zero C
--instance [has_zero_object.{v} C] : has_zero C := ⟨⊤_ C⟩

instance op_initial : has_initial.{v} Cᵒᵖ := { has_colimits_of_shape := 
{ has_colimit := λ F, { cocone := { X := op (⊤_ C),
  ι := { app := by obviously,
  naturality' := by obviously } },
  is_colimit := { desc := λ s, (terminal.from (unop s.X)).op,
  fac' := by obviously,
  uniq' := λ s m _, begin
    suffices : m.unop = (limits.terminal.from (unop (s.X))), from congr_arg has_hom.hom.op this,
    have h := (limits.unique_to_terminal (unop (s.X))).uniq,
    rw [h (limits.terminal.from (unop (s.X))), h (has_hom.hom.unop m)]
  end }}}}

instance op_terminal : has_terminal.{v} Cᵒᵖ := { has_limits_of_shape :=
{ has_limit := λ F, { cone := { X := op (⊥_ C),
  π := { app := by obviously,
  naturality' := by obviously } },
  is_limit := { lift := λ s, (initial.to (unop s.X)).op,
  fac' := by obviously,
  uniq' := λ s m _, begin
    suffices : m.unop = (limits.initial.to (unop (s.X))), from congr_arg has_hom.hom.op this,
    have h := (limits.unique_from_initial (unop (s.X))).uniq,
    rw [h (limits.initial.to (unop (s.X))), h (has_hom.hom.unop m)]
  end }}}}

lemma terminal_is_initial : (⊥_ Cᵒᵖ) = op (⊤_ C) := rfl
lemma initial_is_terminal : (⊤_ Cᵒᵖ) = op (⊥_ C) := rfl

instance op_zero [has_zero_object.{v} C] : has_zero_object.{v} Cᵒᵖ :=
⟨begin
  rw [terminal_is_initial, initial_is_terminal],
  exact congr_arg op ((has_zero_object.terminal_eq_initial.{v} C).symm)
end⟩

section
variables {C} [has_zero_object.{v} C]

lemma zero.eq_terminal : _0 C = ⊤_ C := rfl

lemma zero.eq_initial : _0 C = ⊥_ C :=
by rw [zero.eq_terminal, has_zero_object.terminal_eq_initial.{v} C]

lemma zero.autodual : _0 Cᵒᵖ = op (_0 C) :=
by rw [zero.eq_terminal, initial_is_terminal, zero.eq_initial]

abbreviation zero.from (P : C) : P ⟶ _0 C := terminal.from P

abbreviation zero.to (P : C) : _0 C ⟶ P :=
by { rw zero.eq_initial, exact initial.to P }

instance unique_to_zero (P : C) : unique (P ⟶ _0 C) :=
limits.unique_to_terminal P

instance unique_from_zero (P : C) : unique (_0 C ⟶ P) :=
by { rw zero.eq_initial, exact limits.unique_from_initial P }

lemma zero.from_dual (P : C) : eq_to_hom (zero.autodual) ≫ (zero.from P).op = zero.to (op P) :=
begin
  rw (limits.unique_from_zero (op P)).uniq (zero.to (op P)),
  rw (limits.unique_from_zero (op P)).uniq (eq_to_hom (zero.autodual) ≫ (zero.from P).op)
end

lemma zero.to_dual (P : C) : (zero.to P).op ≫ eq_to_hom (zero.autodual).symm = zero.from (op P) :=
begin
  rw (limits.unique_to_zero (op P)).uniq (zero.from (op P)),
  rw (limits.unique_to_zero (op P)).uniq ((zero.to P).op ≫ eq_to_hom (zero.autodual).symm),
end

/- Borceux 2, Def. 1.1.2 -/
abbreviation zero_mor (P : C) (Q : C) : P ⟶ Q :=
(zero.from P) ≫ (zero.to Q)

instance {P Q : C} : has_zero (P ⟶ Q) := ⟨zero_mor P Q⟩

lemma zero.from_zero {P : C} (f : _0 C ⟶ P) : f = 0 :=
by rw [(limits.unique_from_zero P).uniq f, (limits.unique_from_zero P).uniq 0]

lemma zero.to_zero {P : C} (f : P ⟶ _0 C) : f = 0 :=
by rw [(limits.unique_to_zero P).uniq f, (limits.unique_to_zero P).uniq 0]

lemma zero.mor_autodual {P Q : C} : (0 : P ⟶ Q).op = 0 :=
begin
  unfold has_zero.zero,
  delta zero_mor,
  rw [op_comp, ←zero.from_dual, ←zero.to_dual],
  simp
end

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

/- Borceux 2, Prop. 1.1.6 -/
lemma zero_comp' {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} [mono g] (h : f ≫ g = 0) : f = 0 :=
by { rw [←zero_comp P g, cancel_mono] at h, exact h }

/- Dual of Borceux 2, Prop. 1.1.6 -/
lemma comp_zero' {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} [epi f] (h : f ≫ g = 0) : g = 0 :=
by { rw [←comp_zero R f, cancel_epi] at h, exact h }

end 
end category_theory.limits