import category_theory.limits.shapes.terminal category_theory.limits.shapes.equalizers zero

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C] [has_terminal.{v} C] [has_initial.{v} C]
include 𝒞

section
variables {C} {P Q : C} (f : P ⟶ Q) [has_zero_object.{v} C] [has_limit (parallel_pair f 0)]

/- Borceux 2, Def. 1.1.5 -/
abbreviation ker := equalizer f 0
abbreviation ker.ι := equalizer.ι f 0
end

section kernel
variables {C} {P Q : C} (f : P ⟶ Q)

lemma fork_comm {P Q : C} {f g : P ⟶ Q} (s : fork f g) :
    (fork.ι s ≫ f) = (s.π.app walking_parallel_pair.one) :=
by convert @cone.w _ _ _ _ _ s _ _ walking_parallel_pair_hom.left

lemma fork_comm' {P Q : C} {f g : P ⟶ Q} (s : fork f g) :
    (fork.ι s ≫ g) = (s.π.app walking_parallel_pair.one) :=
by convert @cone.w _ _ _ _ _ s _ _ walking_parallel_pair_hom.right

variable [has_zero_object.{v} C]

/- Borceux 2, Prop. 1.1.7 -/
lemma ker_eq_zero [mono f] :
    is_limit (fork.of_ι (0 : _0 C ⟶ P) (by rw [zero_comp, zero_comp]) : fork f 0) :=
⟨λ s, 0,
begin
  intros s j,
  let s' : fork f 0 := s,
  have : s = s', by refl,
  rw this,
  cases j,
  begin
    rw zero_comp,
    refine (@zero_comp' _ _ _ _ _ _ _ _ _ f _ _).symm,
    have : (s'.π).app limits.walking_parallel_pair.zero = fork.ι s', by refl,
    rw this,
    rw fork.condition,
    convert comp_zero _ (limits.fork.ι s'),
  end,
  begin
    rw [zero_comp, ←fork_comm' s'],
    convert (comp_zero _ (limits.fork.ι s')).symm,
  end
end,
λ _ m _, zero.to_zero m⟩

--set_option pp.implicit true
set_option trace.check true

/- Borceux 2, Prop. 1.1.8 -/
lemma ker_eq_id : is_limit.{v} (fork.of_ι (𝟙 P) (by simp) : fork.{v} (0 : P ⟶ Q) (0 : P ⟶ Q)) :=
{lift := λ s, s.π.app limits.walking_parallel_pair.zero,
fac' := λ s j,
begin
  cases j,
  begin
    simp only [fork.of_ι_app_zero, category.id_comp],
    exact @category.comp_id C _ _ P ((s.π).app limits.walking_parallel_pair.zero.{v})
  end,
  begin
    simp only [category.id_comp, fork.of_ι_app_one],
    rw ←fork_comm,
    rw @comp_zero _ _ _ _ _ _ P Q (limits.fork.ι.{v u} s),
    rw ←category.assoc,
    rw @comp_zero _ _ _ _ _ _ P Q ((s.π).app limits.walking_parallel_pair.zero ≫ 𝟙 P)
  end
end,
uniq' := λ s m h,
begin
  rw ←(h limits.walking_parallel_pair.zero.{v}),
  simp only [fork.of_ι_app_zero, category.id_comp],
  rw @category.comp_id C _ _ P m
end}

end kernel
end category_theory.limits