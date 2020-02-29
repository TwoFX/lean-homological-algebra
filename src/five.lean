import linear_algebra.basic

open linear_map

section four
variables {R : Type*} [ring R]
variables {A : Type*} {B : Type*} {C : Type*} {D : Type*}
variables [add_comm_group A] [add_comm_group B] [add_comm_group C] [add_comm_group D]
variables [module R A] [module R B] [module R C] [module R D]
variables {A' : Type*} {B' : Type*} {C' : Type*} {D' : Type*}
variables [add_comm_group A'] [add_comm_group B'] [add_comm_group C'] [add_comm_group D']
variables [module R A'] [module R B'] [module R C'] [module R D']
variables {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D}
variables {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'} {h' : C' →ₗ[R] D'}
variables {α : A →ₗ[R] A'} {β : B →ₗ[R] B'} {γ : C →ₗ[R] C'} {δ : D →ₗ[R] D'}
variables (fg : f.range = g.ker) (gh : g.range = h.ker)
variables (fg' : f'.range = g'.ker) (gh' : g'.range = h'.ker)
variables (comm₁ : f' ∘ α = β ∘ f) (comm₂ : g' ∘ β = γ ∘ g) (comm₃ : h' ∘ γ = δ ∘ h)

include fg gh fg' gh' comm₁ comm₂ comm₃

lemma four (hα : α.range = ⊤) (hγ : γ.range = ⊤) (hδ : δ.ker = ⊥) : β.range = ⊤ :=
begin
  apply range_eq_top.2,
  intro b',
  set c' := g' b',
  cases range_eq_top.1 hγ c' with c hc,
  set d := h c,
  have hδd : δ d = 0,
  { change (δ ∘ h) c = 0,
    rw ←comm₃,
    rw function.comp_apply,
    rw hc,
    rw ←mem_ker,
    rw ←gh',
    apply submodule.mem_map_of_mem,
    trivial, },
  have hd : d = 0 := ker_eq_bot'.1 hδ d hδd,
  have hhc : c ∈ h.ker := mem_ker.2 hd,
  rw ←gh at hhc,
  cases hhc with b hb,
  replace hb := hb.2,
  rw ←hb at hc,
  rw ←function.comp_apply γ g at hc,
  rw ←comm₂ at hc,
  have hβb : β b - b' ∈ g'.ker := sub_mem_ker_iff.2 hc,
  rw ←fg' at hβb,
  cases mem_range.1 hβb with a' ha',
  cases range_eq_top.1 hα a' with a ha,
  rw ←ha at ha',
  rw ←function.comp_apply f' α at ha',
  rw comm₁ at ha',
  rw function.comp_apply at ha',
  use b - f a,
  simp [ha'],
end

lemma four' (hα : α.range = ⊤) (hβ : β.ker = ⊥) (hδ : δ.ker = ⊥) : γ.ker = ⊥ :=
begin
  apply ker_eq_bot'.2,
  intros c hc,
  have hhc : c ∈ ker h,
  { apply mem_ker.2,
    apply ker_eq_bot'.1 hδ (h c),
    rw ←function.comp_apply δ h,
    rw ←comm₃,
    rw function.comp_apply,
    rw hc,
    rw map_zero, },
  rw ←gh at hhc,
  cases hhc with b hb,
  replace hb := hb.2,
  set b' := β b,
  have hgb' : b' ∈ ker g',
  { apply mem_ker.2,
    change (g' ∘ β) b = 0,
    rw comm₂,
    rw function.comp_apply,
    rw hb,
    rw hc, },
  rw ←fg' at hgb',
  cases hgb' with a' ha',
  replace ha' := ha'.2,
  cases range_eq_top.1 hα a' with a ha,
  rw ←ha at ha',
  rw ←function.comp_apply f' α at ha',
  rw comm₁ at ha',
  have ha₀ : f a = b := ker_eq_bot.1 hβ ha',
  have hb₀ : b ∈ f.range,
  { rw ←ha₀,
    apply submodule.mem_map_of_mem,
    trivial, },
  rw fg at hb₀,
  rw ←hb,
  apply mem_ker.1,
  assumption,
end

#check eq.rec

end four

section five
variables {R : Type*} [ring R]
variables {A : Type*} {B : Type*} {C : Type*} {D : Type*} {E :  Type*}
variables [add_comm_group A] [add_comm_group B] [add_comm_group C] [add_comm_group D] [add_comm_group E]
variables [module R A] [module R B] [module R C] [module R D] [module R E]
variables {A' : Type*} {B' : Type*} {C' : Type*} {D' : Type*} {E' : Type*}
variables [add_comm_group A'] [add_comm_group B'] [add_comm_group C'] [add_comm_group D'] [add_comm_group E']
variables [module R A'] [module R B'] [module R C'] [module R D'] [module R E']
variables {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D} {i : D →ₗ[R] E}
variables {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'} {h' : C' →ₗ[R] D'} {i' : D' →ₗ[R] E'}
variables {α : A →ₗ[R] A'} {β : B ≃ₗ[R] B'} {γ : C →ₗ[R] C'} {δ : D ≃ₗ[R] D'} (ε : E →ₗ[R] E')
variables (fg : f.range = g.ker) (gh : g.range = h.ker) (hi : h.range = i.ker)
variables (fg' : f'.range = g'.ker) (gh' : g'.range = h'.ker) (hi' : h'.range = i'.ker)
variables (comm₁ : f' ∘ α = β ∘ f) (comm₂ : g' ∘ β = γ ∘ g) (comm₃ : h' ∘ γ = δ ∘ h) (comm₄ : i' ∘ δ = ε ∘ i)

noncomputable def five (hα : α.range = ⊤) (hε : ε.ker = ⊥) : C ≃ₗ[R] C' :=
linear_equiv.of_bijective γ
(four' fg gh fg' gh' comm₁ comm₂ comm₃ hα (linear_equiv.ker β) (linear_equiv.ker δ))
(four gh hi gh' hi' comm₂ comm₃ comm₄ (linear_equiv.range β) (linear_equiv.range δ) hε)

end five
