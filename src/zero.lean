import category_theory.limits.shapes.terminal category_theory.limits.shapes.equalizers

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_initial.{v} C]
include 𝒞


class has_zero_object :=
(terminal_eq_initial : (⊤_ C) = ⊥_ C)

abbreviation zero [has_zero_object.{v} C] : C := ⊤_ C

notation `_0` C:20 := zero C
--instance [has_zero_object.{v} C] : has_zero C := ⟨⊤_ C⟩

section
variables {C}

abbreviation zero.from [has_zero_object.{v} C] (P : C) : P ⟶ _0 C := terminal.from P
abbreviation zero.to [has_zero_object.{v} C] (P : C) : _0 C ⟶ P :=
by { delta zero, rw has_zero_object.terminal_eq_initial.{v} C, exact initial.to P }

instance unique_to_zero [has_zero_object.{v} C] (P : C) : unique (P ⟶ _0 C) :=
by { delta zero, exact limits.unique_to_terminal P }

instance unique_from_zero [has_zero_object.{v} C] (P : C) : unique (_0 C ⟶ P) :=
by { delta zero, rw has_zero_object.terminal_eq_initial.{v} C, exact limits.unique_from_initial P }

abbreviation zero_mor [has_zero_object.{v} C] (P : C) (Q : C) : P ⟶ Q :=
(zero.from P) ≫ (zero.to Q)

instance morphisms.have_zero [has_zero_object.{v} C] {P Q : C} : has_zero (P ⟶ Q) := ⟨zero_mor P Q⟩
--notation P ` ⟶₀ ` Q:10 := zero_mor P Q

/- Borceux 2, Prop. 1.1.4 -/
@[simp] lemma zero_comp [has_zero_object.{v} C] {P Q R : C} (g : Q ⟶ R) : (0 : P ⟶ Q) ≫ g = 0 :=
begin
  unfold has_zero.zero,
  rw category.assoc',
  rw (limits.unique_from_zero R).uniq (zero.to Q ≫ g),
  delta zero_mor,
  rw (limits.unique_from_zero R).uniq (zero.to R)
end

/- Borceux 2, Prop. 1.1.4 -/
@[simp] lemma comp_zero [has_zero_object.{v} C] {P Q R : C} (f : P ⟶ Q) : f ≫ (0 : Q ⟶ R) = 0 :=
begin
  unfold has_zero.zero,
  rw ←category.assoc',
  rw (limits.unique_to_zero P).uniq (f ≫ zero.from Q),
  delta zero_mor,
  rw (limits.unique_to_zero P).uniq (zero.from P)
end

/- Borceux 2, Prop 1.1.6 -/
lemma zero_comp' [has_zero_object.{v} C] {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} [mono g] (h : f ≫ g = 0) : f = 0 :=
by { rw [←zero_comp g, cancel_mono g] at h, exact h }

section kernel
variables {P Q : C} (f : P ⟶ Q) [has_zero_object.{v} C] [has_limit (parallel_pair f 0)]

/- Borceux 2, Def. 1.1.5 -/
abbreviation ker := equalizer f 0
abbreviation ker.ι := equalizer.ι f 0

lemma fork_comm {P Q : C} {f g : P ⟶ Q} (s : fork f g) :
    (fork.ι s ≫ f) = (s.π.app walking_parallel_pair.one) :=
by convert @cone.w _ _ _ _ _ s _ _ walking_parallel_pair_hom.left

lemma fork_comm' {P Q : C} {f g : P ⟶ Q} (s : fork f g) :
    (fork.ι s ≫ g) = (s.π.app walking_parallel_pair.one) :=
by convert @cone.w _ _ _ _ _ s _ _ walking_parallel_pair_hom.right

/- Borceux 2, Prop 1.1.7 -/
lemma ker_eq_zero [mono f] : ker f ≅ _0 C :=
begin
  let zero_cone : cone (parallel_pair f 0) := { X := _0 C, π := { app := λ X, 0 }, },
  suffices : is_limit zero_cone,
  begin
    have := functor.map_iso cones.forget (is_limit.unique_up_to_iso (limit.is_limit (parallel_pair f 0)) this),
    simp only [cones.forget_obj] at this,
    exact this,
  end,
  exact {
    lift := λ s, 0,
    fac' := begin
      intros s j,
      rw zero_comp,
      let s' : fork f 0 := s,
      have : s = s', by refl,
      rw this,
      cases j,
      begin
        refine (@zero_comp' _ _ _ _ _ _ _ _ _ f _ _).symm,
        have : (s'.π).app limits.walking_parallel_pair.zero = fork.ι s', by refl,
        rw this,
        rw fork.condition,
        convert comp_zero (limits.fork.ι s'),
      end,
      begin
        rw ←fork_comm' s',
        convert (comp_zero (limits.fork.ι s')).symm,
      end
    end,
    uniq' := begin
      intros, have t : unique (s.X ⟶ _0 C), by apply_instance,
      have u := t.uniq m,
      have v := t.uniq 0,
      cc,
    end
  }
end

lemma ker_eq_id [has_limit (parallel_pair (0 : P ⟶ Q) 0)] : ker (0 : P ⟶ Q) ≅ P :=
begin
  let id_fork : fork (0 : P ⟶ Q) 0 := fork.of_ι (𝟙 P) (by simp),
  suffices : is_limit id_fork,
  begin
    have := functor.map_iso cones.forget (is_limit.unique_up_to_iso (limit.is_limit (parallel_pair 0 0)) this),
    simp only [cones.forget_obj] at this,
    exact this,
  end,
  exact {
    lift := λ s, by convert s.π.app limits.walking_parallel_pair.zero,
    fac' := begin
      intros s j,
      cases j,
      simp only [fork.of_ι_app_zero, comp_zero],
    end
  }
end
end kernel



end
end category_theory.limits