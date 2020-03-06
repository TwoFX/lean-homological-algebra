import linear_algebra.basic diagram_chase

open linear_map

section part_one
variables {R : Type*} [ring R]
variables {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
variables [add_comm_group A] [add_comm_group B] [add_comm_group A'] [add_comm_group B']
variables [module R A] [module R B] [module R A'] [module R B']
variables {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {α : A →ₗ[R] A'} {β : B →ₗ[R] B'}
variables (comm : g ∘ α = β ∘ f)
include comm

lemma nine₁ (hg : ker g = ⊥) (hα : ker α = ⊥) (hβ : ker β = ⊥) : ker f = ⊥ :=
ker_eq_bot'.2 $ λ a ha, by chase a [ha] using [α] with a' only 0 = 0

lemma nnine₁ (hg : ker g = ⊥) (hα : ker α = ⊥) (hβ : ker β = ⊥) : ker f = ⊥ :=
ker_eq_bot'.2 $ λ a ha, ker_eq_bot'.1 hα a $ ker_eq_bot'.1 hg (α a) $
by rw [←function.comp_apply g α, comm]; simp [ha]

end part_one

section part_two
variables {R : Type*} [ring R]
variables {A₁ : Type*} {A₂ : Type*} {A₃ : Type*}
variables {B₁ : Type*} {B₂ : Type*} {B₃ : Type*}
variables {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
variables [add_comm_group A₁] [add_comm_group A₂] [add_comm_group A₃]
variables [add_comm_group B₁] [add_comm_group B₂] [add_comm_group B₃]
variables [add_comm_group C₁] [add_comm_group C₂] [add_comm_group C₃]
variables [module R A₁] [module R A₂] [module R A₃]
variables [module R B₁] [module R B₂] [module R B₃]
variables [module R C₁] [module R C₂] [module R C₃]
variables {f₁ : A₁ →ₗ[R] B₁} {g₁ : B₁ →ₗ[R] C₁}
variables {f₂ : A₂ →ₗ[R] B₂} {g₂ : B₂ →ₗ[R] C₂}
variables {f₃ : A₃ →ₗ[R] B₃} {g₃ : B₃ →ₗ[R] C₃}
variables {α₁ : A₁ →ₗ[R] A₂} {β₁ : B₁ →ₗ[R] B₂} {γ₁ : C₁ →ₗ[R] C₂}
variables {α₂ : A₂ →ₗ[R] A₃} {β₂ : B₂ →ₗ[R] B₃} {γ₂ : C₂ →ₗ[R] C₃}
variables (comm₁ : β₁ ∘ f₁ = f₂ ∘ α₁) (comm₂ : γ₁ ∘ g₁ = g₂ ∘ β₁)
variables (comm₃ : β₂ ∘ f₂ = f₃ ∘ α₂) (comm₄ : γ₂ ∘ g₂ = g₃ ∘ β₂)

variables (hα₁ : ker α₁ = ⊥) (hβ₁ : ker β₁ = ⊥) (hγ₁ : ker γ₁ = ⊥)
variables (hα₂ : range α₂ = ⊤) (hβ₂ : range β₂ = ⊤) (hγ₂ : range γ₁ = ⊤)
variables (hα : range α₁ = ker α₂) (hβ : range β₁ = ker β₂) (hγ : range γ₁ = ker γ₂)

variables (hf₂ : ker f₂ = ⊥) (hf₃ : ker f₃ = ⊥)
variables (hg₂ : range g₂ = ⊤) (hg₃ : range g₃ = ⊤)
variables (fg₂ : range f₂ = ker g₂) (fg₃ : range f₃ = ker g₃)

include comm₁ comm₂ comm₃ comm₄
include hα₁ hβ₁ hγ₁
include hα₂ hβ₂ hγ₂
include hα hβ hγ
include hf₂ hf₃ hg₂ hg₃ fg₂ fg₃

lemma nine₂ : range f₁ = ker g₁ :=
begin
  apply le_antisymm,
  { rintros b ⟨a, ⟨_, ah⟩⟩,
    apply mem_ker.2,
    rw ← ah,
    apply ker_eq_bot.1 hγ₁,
    rw ccongr comm₂ (f₁ a),
    rw ccongr comm₁ a,
    rw exact_apply fg₂ (α₁ a),
    rw map_zero, },
  { intros b bh',
    have bh := mem_ker.1 bh',
    chase' b [bh] using [β₁, f₂, α₁] with b' a' a only f₁ a = b,
    exact ⟨a, ⟨trivial, h_52⟩⟩, }
end

lemma nine₃  : range g₁ = ⊤ :=
range_eq_top.2 $ λ c,
begin
  chase' c [] using [γ₁, g₂, β₂, f₃, α₂, f₂] with c' b' b'' a'' a' bb only β₂ b' = β₂ bb,
  have hbbb := mem_ker.1 (sub_mem_ker_iff.2 h_48),
  have hbb : g₂ bb = 0, by transitivity',
  have hbx : g₂ (b' - bb) = g₂ b', by rw [map_sub, hbb, sub_zero],
  chase' (b' - bb) [hbbb] using [β₁] with b only g₁ b = c,
  exact ⟨b, h_86⟩,
end

end part_two