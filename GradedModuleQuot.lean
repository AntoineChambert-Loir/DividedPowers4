import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.Module.GradedModule
import Mathbin.RingTheory.GradedAlgebra.HomogeneousIdeal
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.Ideal.QuotientOperations
import Mathbin.RingTheory.GradedAlgebra.Basic
import Mathbin.Algebra.GradedMulAction
import Mathbin.Algebra.DirectSum.Decomposition
import Mathbin.Algebra.Module.BigOperators

/-!
# Graded modules over a graded ring, homogeneous submodules

This file defines a graded module (given by `ℳ : ι → submodule R M` for a `module R M`, homogeneous submodules, and operations on them (sums, intersections, quotients…)

The ring `R` is  not graded.

At the end, one adds an `graded_ring ℳ` for `ℳ : ι → submodule R A`, an `A`-algebra structure on `M` which is compatible with the `R`-module structure, and the multiplication is compatible with the gradings. 

The case of homogeneous submodules of a graded ring follows.

WORK IN PROGRESS

Question : should there be a variant “without R” ?
Mathematically, this is equivalent with having R = ℕ,
but it may be painful to have to use `to_nat_module`…

Question : There is no reason that the indices of the grading of the ring are the same as for the module, 
one should just have an `add_smul_action : ι → θ → θ`

Question : What about multiplicative weights?

-/


open SetLike DirectSum Set

open scoped BigOperators Pointwise DirectSum

variable {ι σ τ R A M : Type _}

variable [Semiring R]

variable [DecidableEq ι] [AddMonoid ι]

variable [AddCommMonoid M] [Module R M]

-- variables [comm_ring A] [algebra R A] [module A M] [is_scalar_tower R A M]
-- variables (ℳ : ι → submodule R A)
variable (ℳ : ι → Submodule R M)

section GradedModule

-- variables [set_like.graded_monoid ℳ] [graded_ring ℳ] [set_like.has_graded_smul ℳ ℳ]
-- example : set_like.has_graded_smul ℳ ℳ := 
-- set_like.has_graded_mul.to_has_graded_smul ℳ
/-  Trop lourd
 class graded_module {ι : Type*}  [decidable_eq ι] [add_monoid ι]
  {A R M : Type*} 
  [comm_semiring R] [comm_semiring A] [add_comm_monoid M] [algebra R A]
  [graded_algebra ℳ]
  [module R M] [module A M] [is_scalar_tower R A M]
  {σ : Type*} [set_like σ A] [add_submonoid_class σ A] [submodule_class σ R A] (ℳ : ι → σ) 
  {τ : Type*} [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ) :=
(to_decomposition : direct_sum.decomposition ℳ)
(to_graded_smul : set_like.has_graded_smul ℳ ℳ)
 -/
class GradedModule {ι : Type _} [DecidableEq ι] [AddMonoid ι] {R M : Type _} [Semiring R]
    [AddCommMonoid M] [Module R M] {τ : Type _} [SetLike τ M] [AddSubmonoidClass τ M]
    [SMulMemClass τ R M] (ℳ : ι → τ) extends DirectSum.Decomposition ℳ
#align graded_module GradedModule

variable [GradedModule ℳ]

/-- The projection maps of a graded module -/
def GradedModule.proj (i : ι) : M →+ M :=
  (AddSubmonoidClass.Subtype (ℳ i)).comp
    ((DFinsupp.evalAddMonoidHom i).comp <| AddEquiv.toAddMonoidHom <| DirectSum.decomposeAddEquiv ℳ)
#align graded_module.proj GradedModule.proj

@[simp]
theorem GradedModule.proj_apply (i : ι) (r : M) :
    GradedModule.proj ℳ i r = (decompose ℳ r : ⨁ i, ℳ i) i :=
  rfl
#align graded_module.proj_apply GradedModule.proj_apply

theorem GradedModule.proj_recompose (r : ⨁ i, ℳ i) (i : ι) :
    GradedModule.proj ℳ i ((decompose ℳ).symm r) = (decompose ℳ).symm (DirectSum.of _ i (r i)) := by
  rw [GradedModule.proj_apply, decompose_symm_of, Equiv.apply_symm_apply]
#align graded_module.proj_recompose GradedModule.proj_recompose

theorem GradedModule.mem_support_iff [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) (i : ι) :
    i ∈ (decompose ℳ r).support ↔ GradedModule.proj ℳ i r ≠ 0 :=
  DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.Not.symm
#align graded_module.mem_support_iff GradedModule.mem_support_iff

end GradedModule

section HomogeneousDef

variable [GradedModule ℳ]

variable {R}

/- An `N : submodule R M` is homogeneous if for every `r ∈ N`, all homogeneous components
  of `r` are in `N`. -/
def Submodule.IsHomogeneous [GradedModule ℳ] (N : Submodule R M) : Prop :=
  ∀ (i : ι) ⦃r : M⦄, r ∈ N → (DirectSum.decompose ℳ r i : M) ∈ N
#align submodule.is_homogeneous Submodule.IsHomogeneous

/-- For any `module R M`, we collect the homogeneous submodules of `M` into a type. -/
structure HomogeneousSubmodule extends Submodule R M where
  is_homogeneous' : Submodule.IsHomogeneous ℳ to_submodule
#align homogeneous_submodule HomogeneousSubmodule

variable {ℳ}

theorem HomogeneousSubmodule.isHomogeneous (N : HomogeneousSubmodule ℳ) :
    N.toSubmodule.Homogeneous ℳ :=
  N.is_homogeneous'
#align homogeneous_submodule.is_homogeneous HomogeneousSubmodule.isHomogeneous

theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule ℳ → Submodule R M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ (h : x = y) => by simp [h]
#align homogeneous_submodule.to_submodule_injective HomogeneousSubmodule.toSubmodule_injective

instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule ℳ) M
    where
  coe N := N.toSubmodule
  coe_injective' N P h := HomogeneousSubmodule.toSubmodule_injective <| SetLike.coe_injective h
#align homogeneous_submodule.set_like HomogeneousSubmodule.setLike

@[ext]
theorem HomogeneousSubmodule.ext {N P : HomogeneousSubmodule ℳ}
    (h : N.toSubmodule = P.toSubmodule) : N = P :=
  HomogeneousSubmodule.toSubmodule_injective h
#align homogeneous_submodule.ext HomogeneousSubmodule.ext

@[simp]
theorem HomogeneousSubmodule.mem_iff {N : HomogeneousSubmodule ℳ} {x : M} :
    x ∈ N.toSubmodule ↔ x ∈ N :=
  Iff.rfl
#align homogeneous_submodule.mem_iff HomogeneousSubmodule.mem_iff

end HomogeneousDef

section HomogeneousCore

-- variables [semiring R] [add_comm_monoid M] [module R M]
-- variables [set_like τ M]  (ℳ : ι → τ)
variable (N : Submodule R M)

variable {R}

/-- For any `N : submodule R M`, not necessarily homogeneous, `N.homogeneous_core' ℳ`
is the largest homogeneous submodule of `M` contained in `N`, as a submodule. -/
def Submodule.homogeneousCore' (N : Submodule R M) : Submodule R M :=
  Submodule.span R (coe '' ((coe : Subtype (Homogeneous ℳ) → M) ⁻¹' N))
#align submodule.homogeneous_core' Submodule.homogeneousCore'

theorem Submodule.homogeneousCore'_mono : Monotone (Submodule.homogeneousCore' ℳ) :=
  fun N P N_le_P => Submodule.span_mono <| Set.image_subset _ fun x => @N_le_P _
#align submodule.homogeneous_core'_mono Submodule.homogeneousCore'_mono

theorem Submodule.homogeneousCore'_le : N.homogeneousCore' ℳ ≤ N :=
  Submodule.span_le.2 <| image_preimage_subset _ _
#align submodule.homogeneous_core'_le Submodule.homogeneousCore'_le

end HomogeneousCore

section IsHomogeneousSubmoduleDefs

-- variables [semiring R] [add_comm_monoid M] [module R M]
-- variables [set_like τ M] [add_submonoid_class τ M] [submodule_class τ R M] (ℳ : ι → τ)
-- variables [decidable_eq ι] [add_monoid ι] [graded_module ℳ]
variable [GradedModule ℳ]

variable (N : Submodule R M)

variable {R}

theorem Submodule.isHomogeneous_iff_forall_subset :
    N.Homogeneous ℳ ↔ ∀ i, (N : Set M) ⊆ GradedModule.proj ℳ i ⁻¹' N :=
  Iff.rfl
#align submodule.is_homogeneous_iff_forall_subset Submodule.isHomogeneous_iff_forall_subset

theorem Submodule.isHomogeneous_iff_subset_iInter :
    N.Homogeneous ℳ ↔ (N : Set M) ⊆ ⋂ i, GradedModule.proj ℳ i ⁻¹' ↑N :=
  subset_iInter_iff.symm
#align submodule.is_homogeneous_iff_subset_Inter Submodule.isHomogeneous_iff_subset_iInter

/- --  Plus tard, lorsqu'il y aura un anneau gradué 
lemma submodule.mul_homogeneous_element_mem_of_mem
  {I : ideal A} (r x : A) (hx₁ : is_homogeneous ℳ x) (hx₂ : x ∈ I) (j : ι) :
  graded_ring.proj ℳ j (r * x) ∈ I :=
begin
  classical,
  rw [←direct_sum.sum_support_decompose ℳ r, finset.sum_mul, map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (direct_sum.decompose ℳ r k : A) * x ∈ ℳ (k + i) := graded_monoid.mul_mem
    (set_like.coe_mem _) hi,
  erw [graded_ring.proj_apply, direct_sum.decompose_of_mem ℳ mem₁,
    coe_of_apply, set_like.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end -/
theorem Submodule.isHomogeneousSpan (s : Set M) (h : ∀ x ∈ s, Homogeneous ℳ x) :
    (Submodule.span R s).Homogeneous ℳ := by
  rintro i r hr
  rw [Finsupp.span_eq_range_total, LinearMap.mem_range] at hr 
  obtain ⟨f, rfl⟩ := hr
  rw [Finsupp.total_apply, Finsupp.sum, decompose_sum, DFinsupp.finset_sum_apply,
    AddSubmonoidClass.coe_finset_sum]
  refine' Submodule.sum_mem _ _
  rintro ⟨z, hz⟩ hz1
  simp only [decompose_smul, DFinsupp.coe_smul, Pi.smul_apply, Submodule.coe_smul_of_tower,
    Subtype.coe_mk]
  refine' Submodule.smul_mem _ _ _
  obtain ⟨j, hzj⟩ := h z hz
  by_cases hij : i = j
  · rw [hij]
    rw [DirectSum.decompose_of_mem_same]
    exact Submodule.subset_span hz
    exact hzj
  · rw [DirectSum.decompose_of_mem_ne ℳ hzj (Ne.symm hij)]
    exact Submodule.zero_mem _
#align submodule.is_homogeneous_span Submodule.isHomogeneousSpan

/-- For any `N : submodule R M`, not necessarily homogeneous, `N.homogeneous_core' R ℳ`
is the largest homogeneous submodule of `M` contained in `N`.-/
def Submodule.homogeneousCore : HomogeneousSubmodule ℳ :=
  ⟨Submodule.homogeneousCore' ℳ N,
    Submodule.isHomogeneousSpan ℳ _ fun x h => by
      rw [Subtype.image_preimage_coe, mem_inter_iff, mem_coe] at h ; exact h.2⟩
#align submodule.homogeneous_core Submodule.homogeneousCore

theorem Submodule.homogeneousCore_mono : Monotone (Submodule.homogeneousCore ℳ) :=
  Submodule.homogeneousCore'_mono ℳ
#align submodule.homogeneous_core_mono Submodule.homogeneousCore_mono

theorem Submodule.toSubmodule_homogeneousCore_le : (N.homogeneousCore ℳ).toSubmodule ≤ N :=
  Submodule.homogeneousCore'_le ℳ N
#align submodule.to_submodule_homogeneous_core_le Submodule.toSubmodule_homogeneousCore_le

variable {ℳ N}

theorem Submodule.mem_homogeneousCore_of_homogeneous_of_mem {x : M} (h : SetLike.Homogeneous ℳ x)
    (hmem : x ∈ N) : x ∈ N.homogeneousCore ℳ :=
  Submodule.subset_span ⟨⟨x, h⟩, hmem, rfl⟩
#align submodule.mem_homogeneous_core_of_is_homogeneous_of_mem Submodule.mem_homogeneousCore_of_homogeneous_of_mem

theorem Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self (h : N.Homogeneous ℳ) :
    (N.homogeneousCore ℳ).toSubmodule = N :=
  by
  apply le_antisymm (N.homogeneous_core'_le ℳ) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact
    Submodule.sum_mem _ fun j hj => Submodule.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩
#align submodule.is_homogeneous.to_submodule_homogeneous_core_eq_self Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self

@[simp]
theorem HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self (N : HomogeneousSubmodule ℳ) :
    N.toSubmodule.homogeneousCore ℳ = N := by
  ext1 <;> convert Submodule.IsHomogeneous.toSubmodule_homogeneousCore_eq_self N.is_homogeneous
#align homogeneous_submodule.to_submodule_homogeneous_core_eq_self HomogeneousSubmodule.toSubmodule_homogeneousCore_eq_self

variable (ℳ N)

theorem Submodule.IsHomogeneous.iff_eq : N.Homogeneous ℳ ↔ (N.homogeneousCore ℳ).toSubmodule = N :=
  ⟨fun hI => hI.toSubmodule_homogeneousCore_eq_self, fun hI =>
    hI ▸ (Submodule.homogeneousCore ℳ N).2⟩
#align submodule.is_homogeneous.iff_eq Submodule.IsHomogeneous.iff_eq

def homogeneousSet : Set M :=
  {m : M | Homogeneous ℳ m}
#align homogeneous_set homogeneousSet

theorem Submodule.IsHomogeneous.iff_exists :
    N.Homogeneous ℳ ↔ ∃ S : Set (homogeneousSet ℳ), N = Submodule.span R (coe '' S) :=
  by
  rw [Submodule.IsHomogeneous.iff_eq, eq_comm]
  exact ((set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm
#align submodule.is_homogeneous.iff_exists Submodule.IsHomogeneous.iff_exists

end IsHomogeneousSubmoduleDefs

/-! ### Operations
In this section, we show that `submodule.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_submodule`. -/


section Operations

section Semiring

/- 
variables [semiring A] [decidable_eq ι] [add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (ℳ : ι → σ) [graded_ring ℳ]
include A -/
variable [GradedModule ℳ]

variable {R}

namespace Submodule.IsHomogeneous

theorem bot : Submodule.IsHomogeneous ℳ ⊥ := fun i r hr =>
  by
  simp only [Submodule.mem_bot] at hr 
  rw [hr, decompose_zero, zero_apply]
  apply Submodule.zero_mem
#align submodule.is_homogeneous.bot Submodule.IsHomogeneous.bot

theorem top : Submodule.IsHomogeneous ℳ ⊤ := fun i r hr => by simp only [Submodule.mem_top]
#align submodule.is_homogeneous.top Submodule.IsHomogeneous.top

variable {ℳ}

theorem inf {N P : Submodule R M} (HN : N.Homogeneous ℳ) (HP : P.Homogeneous ℳ) :
    (N ⊓ P).Homogeneous ℳ := fun i r hr => ⟨HN _ hr.1, HP _ hr.2⟩
#align submodule.is_homogeneous.inf Submodule.IsHomogeneous.inf

theorem sup {N P : Submodule R M} (HN : N.Homogeneous ℳ) (HP : P.Homogeneous ℳ) :
    (N ⊔ P).Homogeneous ℳ := by
  rw [iff_exists] at HN HP ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HN, HP
  refine' ⟨s₁ ∪ s₂, _⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm
#align submodule.is_homogeneous.sup Submodule.IsHomogeneous.sup

protected theorem supr {κ : Sort _} {f : κ → Submodule R M} (h : ∀ i, (f i).Homogeneous ℳ) :
    (⨆ i, f i).Homogeneous ℳ := by
  simp_rw [iff_exists] at h ⊢
  choose s hs using h
  refine' ⟨⋃ i, s i, _⟩
  simp_rw [Set.image_iUnion, Submodule.span_iUnion]
  congr
  exact funext hs
#align submodule.is_homogeneous.supr Submodule.IsHomogeneous.supr

protected theorem infi {κ : Sort _} {f : κ → Submodule R M} (h : ∀ i, (f i).Homogeneous ℳ) :
    (⨅ i, f i).Homogeneous ℳ := by
  intro i x hx
  simp only [Submodule.mem_iInf] at hx ⊢
  exact fun j => h _ _ (hx j)
#align submodule.is_homogeneous.infi Submodule.IsHomogeneous.infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supr₂ {κ : Sort _} {κ' : κ → Sort _} {f : ∀ i, κ' i → Submodule R M}
    (h : ∀ i j, (f i j).Homogeneous ℳ) : (⨆ (i) (j), f i j).Homogeneous ℳ :=
  IsHomogeneous.supr fun i => IsHomogeneous.supr <| h i
#align submodule.is_homogeneous.supr₂ Submodule.IsHomogeneous.supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infi₂ {κ : Sort _} {κ' : κ → Sort _} {f : ∀ i, κ' i → Submodule R M}
    (h : ∀ i j, (f i j).Homogeneous ℳ) : (⨅ (i) (j), f i j).Homogeneous ℳ :=
  IsHomogeneous.infi fun i => IsHomogeneous.infi <| h i
#align submodule.is_homogeneous.infi₂ Submodule.IsHomogeneous.infi₂

/- warning: submodule.is_homogeneous.Sup clashes with submodule.is_homogeneous.sup -> Submodule.IsHomogeneous.sup
Case conversion may be inaccurate. Consider using '#align submodule.is_homogeneous.Sup Submodule.IsHomogeneous.supₓ'. -/
#print Submodule.IsHomogeneous.sup /-
theorem sup {𝒩 : Set (Submodule R M)} (h : ∀ N ∈ 𝒩, Submodule.IsHomogeneous ℳ N) :
    (sSup 𝒩).Homogeneous ℳ := by rw [sSup_eq_iSup]; exact supr₂ h
#align submodule.is_homogeneous.Sup Submodule.IsHomogeneous.sup
-/

/- warning: submodule.is_homogeneous.Inf clashes with submodule.is_homogeneous.inf -> Submodule.IsHomogeneous.inf
Case conversion may be inaccurate. Consider using '#align submodule.is_homogeneous.Inf Submodule.IsHomogeneous.infₓ'. -/
#print Submodule.IsHomogeneous.inf /-
theorem inf {𝒩 : Set (Submodule R M)} (h : ∀ N ∈ 𝒩, Submodule.IsHomogeneous ℳ N) :
    (sInf 𝒩).Homogeneous ℳ := by rw [sInf_eq_iInf]; exact infi₂ h
#align submodule.is_homogeneous.Inf Submodule.IsHomogeneous.inf
-/

end Submodule.IsHomogeneous

variable {ℳ}

namespace HomogeneousSubmodule

instance : PartialOrder (HomogeneousSubmodule ℳ) :=
  SetLike.partialOrder

instance : Top (HomogeneousSubmodule ℳ) :=
  ⟨⟨⊤, Submodule.IsHomogeneous.top ℳ⟩⟩

instance : Bot (HomogeneousSubmodule ℳ) :=
  ⟨⟨⊥, Submodule.IsHomogeneous.bot ℳ⟩⟩

instance : Sup (HomogeneousSubmodule ℳ) :=
  ⟨fun I J => ⟨_, I.Homogeneous.sup J.Homogeneous⟩⟩

instance : Inf (HomogeneousSubmodule ℳ) :=
  ⟨fun I J => ⟨_, I.Homogeneous.inf J.Homogeneous⟩⟩

instance : SupSet (HomogeneousSubmodule ℳ) :=
  ⟨fun S => ⟨⨆ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.supr₂ fun s _ => s.Homogeneous⟩⟩

instance : InfSet (HomogeneousSubmodule ℳ) :=
  ⟨fun S => ⟨⨅ s ∈ S, toSubmodule s, Submodule.IsHomogeneous.infi₂ fun s _ => s.Homogeneous⟩⟩

@[simp]
theorem coe_top : ((⊤ : HomogeneousSubmodule ℳ) : Set M) = univ :=
  rfl
#align homogeneous_submodule.coe_top HomogeneousSubmodule.coe_top

@[simp]
theorem coe_bot : ((⊥ : HomogeneousSubmodule ℳ) : Set M) = 0 :=
  rfl
#align homogeneous_submodule.coe_bot HomogeneousSubmodule.coe_bot

@[simp]
theorem coe_sup (I J : HomogeneousSubmodule ℳ) : ↑(I ⊔ J) = (I + J : Set M) :=
  Submodule.coe_sup _ _
#align homogeneous_submodule.coe_sup HomogeneousSubmodule.coe_sup

@[simp]
theorem coe_inf (I J : HomogeneousSubmodule ℳ) : (↑(I ⊓ J) : Set M) = I ∩ J :=
  rfl
#align homogeneous_submodule.coe_inf HomogeneousSubmodule.coe_inf

@[simp]
theorem toSubmodule_top : (⊤ : HomogeneousSubmodule ℳ).toSubmodule = (⊤ : Submodule R M) :=
  rfl
#align homogeneous_submodule.to_submodule_top HomogeneousSubmodule.toSubmodule_top

@[simp]
theorem toSubmodule_bot : (⊥ : HomogeneousSubmodule ℳ).toSubmodule = (⊥ : Submodule R M) :=
  rfl
#align homogeneous_submodule.to_submodule_bot HomogeneousSubmodule.toSubmodule_bot

@[simp]
theorem toSubmodule_sup (I J : HomogeneousSubmodule ℳ) :
    (I ⊔ J).toSubmodule = I.toSubmodule ⊔ J.toSubmodule :=
  rfl
#align homogeneous_submodule.to_submodule_sup HomogeneousSubmodule.toSubmodule_sup

@[simp]
theorem toSubmodule_inf (I J : HomogeneousSubmodule ℳ) :
    (I ⊓ J).toSubmodule = I.toSubmodule ⊓ J.toSubmodule :=
  rfl
#align homogeneous_submodule.to_submodule_inf HomogeneousSubmodule.toSubmodule_inf

@[simp]
theorem toSubmodule_sSup (ℐ : Set (HomogeneousSubmodule ℳ)) :
    (sSup ℐ).toSubmodule = ⨆ s ∈ ℐ, toSubmodule s :=
  rfl
#align homogeneous_submodule.to_submodule_Sup HomogeneousSubmodule.toSubmodule_sSup

@[simp]
theorem toSubmodule_sInf (ℐ : Set (HomogeneousSubmodule ℳ)) :
    (sInf ℐ).toSubmodule = ⨅ s ∈ ℐ, toSubmodule s :=
  rfl
#align homogeneous_submodule.to_submodule_Inf HomogeneousSubmodule.toSubmodule_sInf

@[simp]
theorem toSubmodule_iSup {κ : Sort _} (s : κ → HomogeneousSubmodule ℳ) :
    (⨆ i, s i).toSubmodule = ⨆ i, (s i).toSubmodule := by rw [iSup, to_submodule_Sup, iSup_range]
#align homogeneous_submodule.to_submodule_supr HomogeneousSubmodule.toSubmodule_iSup

@[simp]
theorem toSubmodule_iInf {κ : Sort _} (s : κ → HomogeneousSubmodule ℳ) :
    (⨅ i, s i).toSubmodule = ⨅ i, (s i).toSubmodule := by rw [iInf, to_submodule_Inf, iInf_range]
#align homogeneous_submodule.to_submodule_infi HomogeneousSubmodule.toSubmodule_iInf

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem toSubmodule_supr₂ {κ : Sort _} {κ' : κ → Sort _} (s : ∀ i, κ' i → HomogeneousSubmodule ℳ) :
    (⨆ (i) (j), s i j).toSubmodule = ⨆ (i) (j), (s i j).toSubmodule := by
  simp_rw [to_submodule_supr]
#align homogeneous_submodule.to_submodule_supr₂ HomogeneousSubmodule.toSubmodule_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem toSubmodule_infi₂ {κ : Sort _} {κ' : κ → Sort _} (s : ∀ i, κ' i → HomogeneousSubmodule ℳ) :
    (⨅ (i) (j), s i j).toSubmodule = ⨅ (i) (j), (s i j).toSubmodule := by
  simp_rw [to_submodule_infi]
#align homogeneous_submodule.to_submodule_infi₂ HomogeneousSubmodule.toSubmodule_infi₂

@[simp]
theorem eq_top_iff (I : HomogeneousSubmodule ℳ) : I = ⊤ ↔ I.toSubmodule = ⊤ :=
  toSubmodule_injective.eq_iff.symm
#align homogeneous_submodule.eq_top_iff HomogeneousSubmodule.eq_top_iff

@[simp]
theorem eq_bot_iff (I : HomogeneousSubmodule ℳ) : I = ⊥ ↔ I.toSubmodule = ⊥ :=
  toSubmodule_injective.eq_iff.symm
#align homogeneous_submodule.eq_bot_iff HomogeneousSubmodule.eq_bot_iff

instance : CompleteLattice (HomogeneousSubmodule ℳ) :=
  toSubmodule_injective.CompleteLattice _ toSubmodule_sup toSubmodule_inf toSubmodule_sSup
    toSubmodule_sInf toSubmodule_top toSubmodule_bot

instance : Add (HomogeneousSubmodule ℳ) :=
  ⟨(· ⊔ ·)⟩

@[simp]
theorem toSubmodule_add (I J : HomogeneousSubmodule ℳ) :
    (I + J).toSubmodule = I.toSubmodule + J.toSubmodule :=
  rfl
#align homogeneous_submodule.to_submodule_add HomogeneousSubmodule.toSubmodule_add

instance : Inhabited (HomogeneousSubmodule ℳ) where default := ⊥

end HomogeneousSubmodule

end Semiring

section CommSemiring

variable [CommSemiring R]

variable [CommSemiring A]

variable [DecidableEq ι] [AddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

variable [Module A M]

variable (I : Ideal A) (N : Submodule R M)

variable [GradedModule ℳ]

