import algebra.category.Module.basic
import linear_algebra.basic
import abelian
import mod_bot
import mod_mono_epi

open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.additive
open category_theory.limits.walking_parallel_pair

noncomputable theory

universe u

variables (R : Type u) [ring R]

namespace Module

section cokernel
variables (M N : Module R) (f : M ⟶ N)

local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

set_option trace.app_builder true

lemma zero_map_apply (x : M) : ((has_zero_morphisms.has_zero.{u} M N).zero : M ⟶ N) x = 0 :=
begin
  have : (inhabited.default (M ⟶ (of R punit))) = ((0 : M →ₗ[R] punit) : M ⟶ (of R punit)),
  { apply has_zero_object.zero_of_to_zero, },
  conv_lhs { change
    (inhabited.default (of R punit ⟶ N) : of R punit ⟶ N)
    ((inhabited.default (M ⟶ of R punit) : M ⟶ of R punit) x) },
  erw this,
  rw linear_map.zero_apply,
  erw linear_map.map_zero,
end

lemma zero_map : (has_zero_morphisms.has_zero.{u} M N).zero = ((0 : M →ₗ[R] N) : M ⟶ N) :=
begin
  ext,
  rw zero_map_apply,
  simp,
end

def cokernel_cocone : cocone (parallel_pair f 0) :=
{ X := of R f.range.quotient,
  ι :=
  { app := λ j,
    match j with
    | zero := 0
    | one := f.range.mkq
    end,
    naturality' := λ j j' g, by { cases j; cases j'; cases g,
      { refl, },
      { conv_rhs { change (0 : M ⟶ (of R f.range.quotient)) },
        conv_lhs { change ((f ≫ f.range.mkq) : M ⟶ (of R f.range.quotient)) },
        ext,
        simp,
        rw zero_map,
        rw linear_map.zero_apply,
        apply (@linear_map.mem_ker _ _ _ _ _ _ _ _ f.range.mkq (f x)).1,
        rw submodule.ker_mkq,
        exact submodule.mem_map_of_mem trivial, },
      { refl, },
      { refl, } } } }

lemma b (s : cofork f 0) : f.range ≤ (cofork.π s).ker :=
begin
  refine submodule.le_def'.mpr _,
  intros n hn,
  apply linear_map.mem_ker.2,
  cases linear_map.mem_range.1 hn with m hm,
  rw ←hm,
  rw ←function.comp_apply (cofork.π s) f,
  rw ←coe_comp,
  rw cofork.condition,
  erw has_zero_morphisms.zero_comp,
  rw zero_map_apply,
end

def cokernel_is_colimit : is_colimit (cokernel_cocone _ _ _ f) :=
{ desc := λ s, f.range.liftq (cofork.π s) (b _ _ _ f s),
  fac' := λ s j,
  begin
    cases j,
    { erw ←cocone_parallel_pair_right, erw ←cocone_parallel_pair_right,
      rw has_zero_morphisms.zero_comp,
      rw has_zero_morphisms.zero_comp,
      erw has_zero_morphisms.zero_comp,
      refl, },
    { convert f.range.liftq_mkq (cofork.π s) (b _ _ _ f s), }
  end,
  uniq' := λ s m h,
  begin
    ext,
    have u := linear_map.range_eq_top.1 (submodule.range_mkq f.range) x,
    cases u with n hn,
    rw ←hn,
    conv_rhs { rw ←linear_map.comp_apply },
    erw f.range.liftq_mkq (cofork.π s) (b _ _ _ f s),
    have hx := h walking_parallel_pair.one,
    conv_rhs at hx { change cofork.π s },
    conv_lhs at hx { congr, change submodule.mkq f.range },
    rw ←hx,
    refl,  
  end }


end cokernel

section cokernel
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

instance : has_cokernels.{u} (Module R) :=
⟨λ _ _ f, ⟨cokernel_cocone _ _ _ f, cokernel_is_colimit _ _ _ f⟩⟩

end cokernel

section products

def module_has_limit_pair (M N : Module R) : has_limit (pair M N) :=
{ cone := @binary_fan.mk _ _ M N (of R $ M × N) (linear_map.fst R M N) (linear_map.snd R M N),
  is_limit :=
  { lift := λ s, linear_map.pair (s.π.app walking_pair.left) (s.π.app walking_pair.right),
    fac' := λ s j,
    begin
      ext,
      rw coe_comp,
      rw function.comp_apply,
      rw ←linear_map.comp_apply,
      cases j,
      { erw linear_map.fst_pair, },
      { erw linear_map.snd_pair, },
    end,
    uniq' := λ s m h,
    begin
      ext,
      { simp only [linear_map.pair_apply],
        rw ←h walking_pair.left,
        refl, },
      { simp only [linear_map.pair_apply],
        rw ←h walking_pair.right,
        refl, },
    end } }

section

local attribute [instance] module_has_limit_pair

instance : has_binary_products.{u} (Module R) :=
has_binary_products_of_has_limit_pair (Module R)

end

def module_has_colimit_pair (M N : Module R) : has_colimit (pair M N) :=
{ cocone := @binary_cofan.mk _ _ M N (of R $ M × N) (linear_map.inl R M N) (linear_map.inr R M N),
  is_colimit := 
  { desc := λ s, linear_map.copair (s.ι.app walking_pair.left) (s.ι.app walking_pair.right),
    fac' := λ s j,
    begin
      ext,
      rw coe_comp,
      rw function.comp_apply,
      rw ←linear_map.comp_apply,
      cases j,
      { erw linear_map.copair_inl, },
      { erw linear_map.copair_inr, },
    end,
    uniq' := λ s m h,
    begin
      ext,
      erw linear_map.copair_apply,
      erw ←h walking_pair.left,
      erw ←h walking_pair.right,
      simp only [function.comp_app, coe_comp], 
      rw binary_cofan.mk_ι_app_left,
      rw binary_cofan.mk_ι_app_right,
      simp only [linear_map.inl_apply, linear_map.inr_apply],
      erw ←linear_map.map_add,
      conv_rhs { change m ((x.fst + 0, 0 + x.snd))},
      simp only [prod.mk.eta, add_zero, zero_add],
    end } }

section

local attribute [instance] module_has_colimit_pair

instance : has_binary_coproducts.{u} (Module R) :=
has_binary_coproducts_of_has_colimit_pair (Module R)

end

end products

attribute [instance] has_zero_object.zero_morphisms_of_zero_object

section
variables {M N : Module R} (f : M ⟶ N)

lemma kernel_ker : kernel f = f.ker := rfl
lemma cokernel_quot : cokernel f = of R f.range.quotient := rfl

lemma kernel_ι_subtype : kernel.ι f = f.ker.subtype := rfl

end

instance : abelian.{u} (Module.{u} R) :=
{ hom_group := by apply_instance,
  distrib_left' := λ P Q R f f' g,
    show (f + f') ≫ g = f ≫ g + f' ≫ g, by ext; simp,
  distrib_right' := λ P Q R f g g',
    show f ≫ (g + g') = f ≫ g + f ≫ g', by ext; simp,
  has_zero := by apply_instance,
  has_binary_products := by apply_instance,
  has_binary_coproducts := by apply_instance,
  has_kernels := by apply_instance,
  has_cokernels := by apply_instance,
  mono_is_kernel := λ A B f m,
  { Z := of R f.range.quotient,
    of := f.range.mkq,
    condition := comp_mkq f,
    l := begin
      refine kernel.transport _ _ _ _,
      { haveI := m,
        exact up_equiv' (equiv_range_of_ker_bot' f (ker_eq_bot_of_mono f)), },
      { haveI := m,
        exact equiv_range_of_ker_bot_fac' f (ker_eq_bot_of_mono f), }
    end },
  epi_is_cokernel := λ A B f e,
  { Z := of R f.ker,
    of := f.ker.subtype,
    condition := ker_comp f,
    l := begin
      refine cokernel.transport' _ _ _ _,
      { haveI := e,
        exact up_equiv' (equiv_range_of_range_top f (range_eq_top_of_epi f)), },
      { haveI := e,
        exact equiv_range_of_range_top_fac f (range_eq_top_of_epi f), },
    end } }

end Module