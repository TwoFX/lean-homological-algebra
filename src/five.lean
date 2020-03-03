import linear_algebra.basic
import tactic.tidy
import diagram_chase
import algebra.punit_instances

open linear_map

set_option profiler true

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

include gh fg' comm₁ comm₂ comm₃

section
include gh'
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
end

section
include fg
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

lemma nfour' (hα : α.range = ⊤) (hβ : β.ker = ⊥) (hδ : δ.ker = ⊥) : γ.ker = ⊥ :=
ker_eq_bot'.2 $ assume (c : C) (hc : γ c = 0),
  have hhc : c ∈ h.ker, from mem_ker.2 $ ker_eq_bot'.1 hδ (h c) $ 
    have h' (γ c) = 0, from hc.symm ▸ map_zero h',
    show (δ ∘ h) c = 0, from comm₃ ▸ this,
  match (gh.symm ▸ hhc : c ∈ g.range) with ⟨(b : B), ⟨_, (hb : g b = c)⟩⟩ :=
    have hgb' : β b ∈ g'.ker, from mem_ker.2 $
      have γ (g b) = 0, from hb.symm ▸ hc,
      show (g' ∘ β) b = 0, from comm₂.symm ▸ this,    
    match (fg'.symm ▸ hgb' : β b ∈ f'.range) with ⟨(a' : A'), ⟨_, (ha' : f' a' = β b)⟩⟩ :=
      match range_eq_top.1 hα a' with ⟨(a : A), (ha : α a = a')⟩ :=
        have hb₀ : b ∈ f.range, from ⟨a, ⟨trivial, ker_eq_bot.1 hβ $
          suffices β (f a) = f' (α a), from eq.trans this (ha.symm ▸ ha'),
          show (β ∘ f) a = (f' ∘ α) a, from congr_fun comm₁.symm a⟩⟩,
        show c = 0, from hb ▸ (mem_ker.1 $ fg ▸ hb₀)
      end
    end
  end



lemma nnfour' (hα : range α = ⊤) (hβ : ker β = ⊥) (hδ : ker δ = ⊥) : ker γ = ⊥ :=
-- Let c ∈ C such that γ(c) = 0. We have to show that c = 0.
ker_eq_bot'.2 $ assume (c : C) (hc : γ c = 0), show c = 0, from

  -- Let us first observe that c is in the kernel of h.
  have c ∈ ker h, from
    -- Since δ is injective, it suffices to show that δ(h(c)) = 0,
    suffices (δ ∘ h) c = 0, from mem_ker.2 $ ker_eq_bot'.1 hδ (h c) this,
    -- which is true by commutativity.
    calc δ (h c) = h' (γ c) : congr_fun comm₃.symm c
             ... = h' 0     : congr_arg h' hc
             ... = 0        : map_zero h',
  
  -- By exactness, this gives us a preimage b of c under g
  exists.elim (gh.symm ▸ this : c ∈ range g) $ assume (b : B) ⟨_, (hb : g b = c)⟩,
    -- Now we claim that g'(β(b)) = 0,
    have β b ∈ ker g', from mem_ker.2 $
      -- which is true by commutativity.
      calc g' (β b) = γ (g b) : congr_fun comm₂ b
                ... = γ c     : congr_arg γ hb
                ... = 0       : hc,
    
    -- Again by exactness, we have a preimage a' of β b under f'...
    exists.elim (fg'.symm ▸ this : β b ∈ range f') $ assume (a' : A') ⟨_, (ha' : f' a' = β b)⟩,
      -- ...which in turn, by surjectivity of α, has a preimage a.
      exists.elim (range_eq_top.1 hα a') $ assume (a : A) (ha : α a = a'),
      
      -- We claim that f(a) = b.
      have f a = b, from 
        -- By injectivity of β, we might as well check that β(f(a)) = β(b),
        suffices β (f a) = β b, from ker_eq_bot.1 hβ this,
        -- which is true by commutativity.
        calc β (f a) = f' (α a) : congr_fun comm₁.symm a
                 ... = f' a'    : congr_arg f' ha
                 ... = β b      : ha',
      
      -- But now we are done, since going two steps in an exact sequence is zero.
      calc c = g b     : hb.symm
         ... = g (f a) : congr_arg g this.symm
         ... = 0       : mem_ker.1 $ fg ▸ submodule.mem_map_of_mem trivial

lemma nnnfour' (hα : range α = ⊤) (hβ : ker β = ⊥) (hδ : ker δ = ⊥) : ker γ = ⊥ :=
ker_eq_bot'.2 $ λ c hc,
begin
  have h₀ : h' 0 = 0, from map_zero _,
  have h₁ : h' (γ c) = h' 0, from congr_arg h' hc,
  have h₂ : h' (γ c) = 0, from eq.trans h₁ h₀,
  have h₃ : δ (h c) = h' (γ c), from congr_fun comm₃.symm c,
  have h₄ : δ (h c) = 0, from eq.trans h₃ h₂,
  have h₅ : h c = 0, from ker_eq_bot'.1 hδ (h c) h₄,
  have h₆ : c ∈ ker h, from mem_ker.2 h₅,
  have h₇ : c ∈ range g, from gh.symm ▸ h₆,
  cases h₇ with b h₈,
  have h₉ : g' (β b) = γ (g b), from congr_fun comm₂ b,
  have h₁₀ : γ (g b) = γ c, from congr_arg γ h₈.2,
  have h₁₁ : g' (β b) = γ c, from eq.trans h₉ h₁₀,
  have h₁₂ : g' (β b) = 0, from eq.trans h₁₁ hc,
  have h₁₃ : β b ∈ ker g', from mem_ker.2 h₁₂,
  have h₁₄ : β b ∈ range f', from fg'.symm ▸ h₁₃,
  cases h₁₄ with a' h₁₅,
  cases range_eq_top.1 hα a' with a h₁₆,
  have h₁₇ : β (f a) = f' (α a), from congr_fun comm₁.symm a,
  have h₁₈ : f' (α a) = f' a', from congr_arg f' h₁₆,
  have h₁₉ : β (f a) = f' a', from eq.trans h₁₇ h₁₈,
  have h₂₀ : β (f a) = β b, from eq.trans h₁₉ h₁₅.2,
  have h₂₁ : f a = b, from ker_eq_bot.1 hβ h₂₀,
  have h₂₂ : g b = g (f a), from congr_arg g h₂₁.symm,
  have h₂₃ : c = g (f a), from eq.trans h₈.2.symm h₂₂,
  have h₂₄ : g (f a) = 0, from exact_apply fg a,
  have h₂₅ : c = 0, from eq.trans h₂₃ h₂₄,
  exact h₂₅,
end


lemma nnnnfour' (hα : range α = ⊤) (hβ : ker β = ⊥) (hδ : ker δ = ⊥) : ker γ = ⊥ :=
ker_eq_bot'.2 $ λ c hc, by chase c [hc] using [g, β, f', α] with b b' a' a only f a = b

#print nnnnfour'

end

section
include gh'

lemma nfour (hα : α.range = ⊤) (hγ : γ.range = ⊤) (hδ : δ.ker = ⊥) : β.range = ⊤ :=
range_eq_top.2 $ λ b',
begin
  chase' b' [] using [g', γ, g] with c' c b only g' (β b) = g' b',
  have hb' : g' (β b - b') = 0 := by rw [map_sub, h_36, sub_self c'],
  chase' (β b - b') [] using [f', α, f] with a' a bb only β bb = β b - b',
  exact ⟨b - bb, by simp [h_74]⟩,
end

#print nfour
end
--#print nnnnfour'



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
(four' fg gh fg' comm₁ comm₂ comm₃ hα (linear_equiv.ker β) (linear_equiv.ker δ))
(four hi gh' hi' comm₂ comm₃ comm₄ (linear_equiv.range β) (linear_equiv.range δ) hε)

end five