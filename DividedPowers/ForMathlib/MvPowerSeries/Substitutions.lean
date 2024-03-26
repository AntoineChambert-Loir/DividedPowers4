import Mathlib.Topology.Algebra.Algebra
import Mathlib.Data.MvPolynomial.CommRing
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc
import DividedPowers.ForMathlib.MvPowerSeries.Evaluation
import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology
import DividedPowers.ForMathlib.Topology.Algebra.Algebra.Basic

--import Mathlib.Topology.UniformSpace.CompleteSeparated

/- # Substitutions in power series

Here we define the substitution of power series into other power series.
We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Evaluation of a power series at adequate elements has been defined
in `DividedPowers.ForMathlib.MvPowerSeries.Evaluation.lean`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having vanishing constant coefficient
* Power series have a linear topology
-/

section DiscreteUniformity

class DiscreteUniformity (α : Type*) [u : UniformSpace α] : Prop where
  eq_principal_idRel : uniformity α = Filter.principal idRel

instance discreteUniformity_bot (α : Type*) : @DiscreteUniformity α ⊥ := by
  apply @DiscreteUniformity.mk α ⊥ rfl

instance discreteTopology_of_discreteUniformity (α : Type*)
    [UniformSpace α] [DiscreteUniformity α] : DiscreteTopology α := by
    rw [discreteTopology_iff_singleton_mem_nhds]
    intro a
    rw [UniformSpace.mem_nhds_iff]
    simp only [Set.subset_singleton_iff, DiscreteUniformity.eq_principal_idRel]
    simp only [Filter.mem_principal, idRel_subset]
    use Set.diagonal α
    simp only [Set.mem_diagonal_iff, implies_true, true_and]
    intro x
    simp only [UniformSpace.ball, Set.mem_preimage, Set.mem_diagonal_iff]
    exact fun a => a.symm

instance bot_uniformAddGroup {R : Type*} [AddGroup R]
    [UniformSpace R] [DiscreteUniformity R] : UniformAddGroup R :=
  { uniformContinuous_sub := fun s hs ↦ by
      simp only [uniformity_prod, DiscreteUniformity.eq_principal_idRel, Filter.comap_principal,
        Filter.inf_principal, Filter.map_principal, Filter.mem_principal, Set.image_subset_iff]
      rintro ⟨⟨x, y⟩, z, t⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, mem_idRel, and_imp]
      rintro ⟨rfl⟩ ⟨rfl⟩
      exact mem_uniformity_of_eq hs rfl }

instance discreteUniformity_complete (α : Type*) [UniformSpace α] [DiscreteUniformity α] : CompleteSpace α :=
  { complete := fun {f} hf ↦ by
      simp [cauchy_iff, bot_uniformity] at hf
      rcases hf with ⟨f_NeBot, hf⟩
      let d := (fun (a : α) ↦ (a, a)) '' Set.univ
      obtain ⟨t, ht, ht'⟩ := hf d (by
        simp only [DiscreteUniformity.eq_principal_idRel, Filter.mem_principal, idRel_subset]
        exact (fun a ↦ Set.mem_image_of_mem (fun a => (a, a)) (Set.mem_univ a)))
      obtain ⟨x, hx⟩ := f_NeBot.nonempty_of_mem ht
      use x
      intro s hs
      apply f.sets_of_superset ht
      intro y hy
      convert mem_of_mem_nhds hs
      apply symm
      simpa only [d, Set.image_univ, Set.range_diag, Set.mem_diagonal_iff] using ht' (Set.mk_mem_prod hx hy)
      }

end DiscreteUniformity

namespace MvPowerSeries

variable {σ : Type*} [DecidableEq σ]
  {R : Type*} [CommRing R]
  -- [TopologicalSpace α] [TopologicalRing α]
  {τ : Type*} [DecidableEq τ]
  {S : Type*} [CommRing S] [Algebra R S]
  -- [TopologicalSpace R] [TopologicalRing R][TopologicalAlgebra α R]

/-- Families of power series which can be substituted -/
structure substDomain (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff : ∀ s, coeff S 0 (a s) = 0
  finite_support : a.support.Finite

variable {a : σ → MvPowerSeries τ S} (ha : substDomain a)

open WithPiTopology WithPiUniformity

local instance : UniformSpace R := ⊥
-- local instance : DiscreteUniformity R := discreteUniformity_bot R
-- local instance : UniformAddGroup R := bot_uniformAddGroup
-- local instance : DiscreteTopology R := discreteTopology_bot R
local instance : TopologicalRing R := DiscreteTopology.topologicalRing

local instance : UniformSpace S := ⊥
local instance : DiscreteUniformity S := discreteUniformity_bot S
-- local instance : CompleteSpace S := discreteUniformity_complete S
-- local instance : DiscreteTopology S := discreteTopology_bot S
-- local instance : UniformAddGroup S := bot_uniformAddGroup
local instance : TopologicalAlgebra R S := inferInstance

-- local instance : UniformSpace (MvPowerSeries τ S) := uniformSpace τ S
-- local instance : UniformAddGroup (MvPowerSeries τ S) := uniformAddGroup τ S
noncomputable local instance : LinearTopology (MvPowerSeries τ S) := isLinearTopology τ S
-- local instance : T2Space (MvPowerSeries τ S) := t2Space τ S
-- local instance : TopologicalRing (MvPowerSeries τ S) := topologicalRing _ _
noncomputable local instance : TopologicalAlgebra R (MvPowerSeries τ S) := by
    refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
local instance : CompleteSpace (MvPowerSeries τ S) := by refine completeSpace τ S

/-- Substibution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  MvPowerSeries.eval₂ (algebraMap _ _) a f

/-- Substibution of power series into a power series -/
noncomputable def substAlgHom : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S :=
  let ha' : evalDomain a := {
    hpow := fun s ↦ tendsto_pow_zero_of_constantCoeff_zero (ha.const_coeff s)
    hcof := tendsto_nhds_of_eventually_eq ha.finite_support }
  MvPowerSeries.aeval ha'

#exit

open MvPowerSeries

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (a) -/
theorem Continuous.tendsto_apply_pow_zero_of_constantCoeff_zero {φ : MvPowerSeries σ α →+* R}
    (hφ : Continuous φ) (s : σ) :
    Filter.Tendsto (fun n : ℕ => φ (X s ^ n)) Filter.atTop (nhds 0) := by
  rw [← φ.map_zero]
  refine' Filter.Tendsto.comp hφ.continuousAt (tendsto_pow_zero_of_constantCoeff_zero _)
  rw [constantCoeff_X]

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (b) -/
theorem Continuous.tendsto_apply_variables_zero_of_cofinite {φ : MvPowerSeries σ α →+* R}
    (hφ : Continuous φ) :
    Filter.Tendsto (fun s : σ => φ (X s)) Filter.cofinite (nhds 0) := by
  rw [← φ.map_zero]
  exact Filter.Tendsto.comp hφ.continuousAt variables_tendsto_zero

end
namespace MvPolynomial

open Set
section Ideals

variable (α : Type*) [CommRing α]

def basis' : (σ →₀ ℕ) → Ideal (MvPolynomial σ α) := fun d =>
  Ideal.span {MvPolynomial.monomial d 1}

/-- The underlying family for the `Ideal.IsBasis` in a multivariate power series ring. -/
def basis : (σ →₀ ℕ) → Ideal (MvPolynomial σ α) := fun d =>
  { carrier   := {f | ∀ e ≤ d, coeff e f = 0} -- monomial e 1 ∣ f
    zero_mem' := fun e _ => by rw [coeff_zero]
    add_mem'  := fun hf hg e he => by rw [coeff_add, hf e he, hg e he, add_zero]
    smul_mem' := fun f g hg e he => by
      classical
      rw [smul_eq_mul, coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero (coeff uv.fst f)
      exact hg  _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he) }

/-- A power series `f` belongs to the ideal `basis σ α d` if and only if `coeff α e f = 0` for all
  `e ≤ d`.  -/
theorem mem_basis (f : MvPolynomial σ α) (d : σ →₀ ℕ) :
    f ∈ basis σ α d ↔ ∀ e ≤ d, coeff e f = 0 := by
  simp only [basis, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq]
  rfl

/-- If `e ≤ d`, then we have the inclusion of ideals `basis σ α d ≤ basis σ α e`. -/
theorem basis_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis σ α d ≤ basis σ α e :=
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))

/-- `basis σ α d ≤ basis σ α e` if and only if `e ≤ d`.-/
theorem basis_le_iff [Nontrivial α] (d e : σ →₀ ℕ) :
    basis σ α d ≤ basis σ α e ↔ e ≤ d := by
  classical
  refine' ⟨_, basis_le _ _⟩
  simp only [basis, Submodule.mk_le_mk, AddSubmonoid.mk_le_mk, setOf_subset_setOf]
  intro h
  rw [← inf_eq_right]
  apply le_antisymm
  . exact inf_le_right
  . by_contra h'
    simp only [AddSubsemigroup.mk_le_mk, setOf_subset_setOf] at h
    specialize h (monomial e 1) _
    . intro e' he'
      simp only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false, ne_eq]
      intro hee'
      rw [← hee'] at he'
      apply h'
      exact le_inf_iff.mpr ⟨he', le_rfl⟩
    apply one_ne_zero' α
    convert h e le_rfl
    simp only [coeff_monomial, ↓reduceIte]

/-- The function `basis σ α` is antitone. -/
theorem basis_antitone : Antitone (basis σ α) := fun _ _ h => basis_le σ α h

-- TODO : generalize to [Ring α]
/-- `MvPowerSeries.basis` is an `Ideal.IsBasis`. -/
theorem idealIsBasis : @Ideal.IsBasis (MvPolynomial σ α) _ _ (basis σ α) :=
  Ideal.IsBasis.ofComm fun d e => by use d ⊔ e; apply Antitone.map_sup_le (basis_antitone σ α)

/-- `MvPowerSeries.basis` is a `RingSubgroupsBasis`. -/
theorem toRingSubgroupsBasis : RingSubgroupsBasis fun d => (basis σ α d).toAddSubgroup :=
  (idealIsBasis σ α).toRingSubgroupsBasis

end Ideals

end MvPolynomial


section foo

variable (Y : σ → R)
    (hY_pow : ∀ s : σ, Filter.Tendsto (fun n : ℕ => (Y s ^ n)) Filter.atTop (nhds 0))
    (hY_cof : ∀ _ : σ, Filter.Tendsto (fun s : σ => (Y s)) Filter.cofinite (nhds 0))
    [τ : UniformSpace R]
    [LinearTopology R]
    [CompleteSpace R] [T2Space R]

namespace MvPolynomial

/-
-- This is MvPolynomial.aeval y
  def aeval_on : MvPolynomial σ α →ₐ[α] R :=
  { toFun     := fun f => MvPolynomial.aeval Y f
    map_one'  := by simp only [map_one]
    map_mul'  := by simp only [map_mul, forall_const]
    map_zero' := by simp only [map_zero]
    map_add'  := by simp only [map_add, forall_const]
    commutes' := by simp only [AlgHom.commutes, forall_const] } -/

local instance topologicalSpace : TopologicalSpace (MvPolynomial σ α) :=
  (idealIsBasis σ α).topology
  --TopologicalSpace.induced MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α

/-- The ring topology on MvPolynomial of a topological ring -/
theorem topologicalRing : @TopologicalRing (MvPolynomial σ α) (idealIsBasis σ α).topology _ :=
  (idealIsBasis σ α).to_topologicalRing

/-

-- NOTE (MI): I am having trouble with this proof because of the `FunLike` hypothesis in
-- `Inducing.continuousAdd` and similar lemmas
/-- The induced ring topology on MvPolynomial of a topological ring -/
theorem induced_topologicalRing : @TopologicalRing (MvPolynomial σ α)
    (TopologicalSpace.induced MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α))
     _ :=
  letI τ := (TopologicalSpace.induced MvPolynomial.toMvPowerSeries
    (MvPowerSeries.topologicalSpace σ α))
  { continuous_add := by
      have h : ContinuousAdd (MvPolynomial σ α) := by
        apply @Inducing.continuousAdd (MvPolynomial σ α) (MvPowerSeries σ α)
          ((MvPolynomial σ α) →ₐ[α] (MvPowerSeries σ α))
        sorry
      exact h.continuous_add
      --apply Inducing.continuousAdd
      --continuousAdd_induced MvPolynomial.toMvPowerSeries
    continuous_mul := sorry
    continuous_neg := sorry }

-- Suggestion : endow MvPolynomial with the linear topology defined by
-- the “same” Ideal.IsBasis and prove :
def toMvPowerSeries_denseInducing [DiscreteTopology α] :
    DenseInducing (@MvPolynomial.toMvPowerSeries σ α _) := {
  induced := by
    let τ := MvPolynomial.topologicalSpace σ α
    let τ' := TopologicalSpace.induced toMvPowerSeries (MvPowerSeries.topologicalSpace σ α)
    rw [TopologicalSpace.eq_iff_nhds_eq]
    suffices ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0 by
    -- mv nhds from 0 to a
      intros S f _hfS -- _hfS is never used
      rw [← add_zero f, @mem_nhds_add_iff _ _ τ,
        @mem_nhds_add_iff _ _ τ' (induced_topologicalRing σ α).to_topologicalAddGroup]
      exact this _
    -- Nhds of zero agree
    intro S
    rw [(RingSubgroupsBasis.hasBasis_nhds (toRingSubgroupsBasis σ α) 0).mem_iff, mem_nhds_induced]
    simp only [sub_zero, Submodule.mem_toAddSubgroup, true_and, coe_zero]
    constructor
    · rintro ⟨i, hi⟩
      use {b | b ∈ MvPowerSeries.basis σ α i}
      exact ⟨(MvPowerSeries.mem_nhds_zero_iff σ α _).mpr ⟨i, by exact fun ⦃a⦄ a => a⟩, hi⟩
    · rintro ⟨U, hU0, hUS⟩
      rw [MvPowerSeries.mem_nhds_zero_iff] at hU0
      obtain ⟨i, hi⟩ := hU0
      use i
      apply le_trans _ hUS
      simp only [Set.le_eq_subset]
      have hi' : toMvPowerSeries ⁻¹' {b | b ∈ MvPowerSeries.basis σ α i} =
        {b | b ∈ basis σ α i} := rfl
      rw [← hi']
      exact Set.preimage_mono hi
  dense   := MvPowerSeries.toMvPowerSeries_denseRange σ α
  /- -- can be deleted ! by
    intro f
    rw [mem_closure_iff]
    intro S hSopen hSf
    have hS : ∃ i, {f + b | b ∈ MvPowerSeries.basis σ α i} ⊆ S := by
      let τ := MvPowerSeries.topologicalSpace σ α
      letI tg := @TopologicalRing.to_topologicalAddGroup _ _ τ (MvPowerSeries.topologicalRing σ α)
      rw [isOpen_iff_mem_nhds] at hSopen
      specialize hSopen _ hSf
      rw [← add_zero f, mem_nhds_add_iff, MvPowerSeries.mem_nhds_zero_iff] at hSopen
      obtain ⟨i, hi⟩ := hSopen
      use i
      intro x ⟨b, hb, hbx⟩
      rw [← hbx]
      exact hi hb
    obtain ⟨i, hi⟩ := hS
    rw [Set.inter_nonempty]
    use MvPowerSeries.trunc' _ i f
    constructor
    · apply hi
      use (- f + (MvPowerSeries.trunc' _ i f))
      constructor
      · simp only [MvPowerSeries.basis, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq, map_add, map_neg, coeff_coe]
        intros e hei
        rw [MvPowerSeries.coeff_trunc', if_pos hei, add_left_neg]
      · simp only [add_neg_cancel_left]
    · simp only [Set.mem_range, coe_inj, exists_eq] -/}

/- lemma aeval_on_continuous : Continuous (aeval_on σ α R Y) := by
    rw [continuous_def]
    intros U hU
    rw [isOpen_iff_mem_nhds]
    intros f hf
    rw [aeval_on]
    simp only [AlgHom.mk_coe]
    sorry
-/
-/

def toMvPowerSeries_induced : TopologicalSpace (MvPolynomial σ α) :=
  (TopologicalSpace.induced (toMvPowerSeries : MvPolynomial σ α → MvPowerSeries σ α) (MvPowerSeries.topologicalSpace σ α))

local instance : TopologicalSpace (MvPolynomial σ α) := toMvPowerSeries_induced σ α

def toMvPowerSeries_inducing : @Inducing _ _
  (toMvPowerSeries_induced σ α) (MvPowerSeries.topologicalSpace σ α) (toMvPowerSeries) where
    induced := rfl

def toMvPowerSeries_denseInducing : @DenseInducing _ _
  (toMvPowerSeries_induced σ α) (MvPowerSeries.topologicalSpace σ α) (toMvPowerSeries) where
    toInducing := toMvPowerSeries_inducing σ α
    dense := by
      have := coeToMvPowerSeries_denseRange (σ := σ) (R := α)
      sorry -- coeToMvPowerSeries_denseRange

def toMvPowerSeries_denseEmbedding : @DenseEmbedding _ _
  (toMvPowerSeries_induced σ α) (MvPowerSeries.topologicalSpace σ α) (toMvPowerSeries) where
    toDenseInducing := toMvPowerSeries_denseInducing σ α
    inj := coe_injective σ α

end MvPolynomial

namespace MvPowerSeries

-- Note (ACL) : what is below is a huge sand box, sorry…
-- Note bis (ACL) : the find Sandbox.lean has better material

open MvPolynomial

local instance : TopologicalRing (MvPowerSeries σ α) := by
  exact topologicalRing σ α

/- local instance : TopologicalRing (MvPolynomial.coeToMvPowerSeries.algHom (σ := σ) (R := α) α).range :=
  (Subalgebra.topologicalSemiring _).toTopologicalRing -/

local instance : TopologicalSpace (MvPolynomial σ α) := toMvPowerSeries_induced σ α

/- `MvPolynomial σ α` is exactly the set of finitely supported
  functions from (σ →₀ ℕ) to α.
  As such, its natural topology is the compact open topology,
  if (σ →₀ ℕ) is given the discrete topology.
  This topology corresponds with a natural uniformity. -/

example : UniformSpace (MvPolynomial σ α) :=
  ContinuousMap.compactConvergenceUniformSpace
example : TopologicalRing (MvPolynomial σ α) where
  continuous_add := Continuous.mk (fun s hs =>
    by sorry)
  continuous_mul := sorry
  continuous_neg := sorry

local instance : UniformSpace α := TopologicalAddGroup.toUniformSpace α

example : UniformAddGroup α :=  by exact comm_topologicalAddGroup_is_uniform

example : TopologicalRing (MvPolynomial σ α) := by sorry

example : UniformSpace (MvPolynomial σ α) := by
  refine instUniformSpace (MvPolynomial σ α)
  sorry

example : @UniformInducing (MvPolynomial σ α) _ _ _ (toMvPowerSeries) := by
  apply?

noncomputable def aeval : MvPowerSeries σ α → R :=
    (toMvPowerSeries_denseInducing σ α).extend (MvPolynomial.aeval Y)

/- noncomputable def aeval_on [DiscreteTopology α] : MvPowerSeries σ α →ₐ[α] R :=
  { toFun     := DenseInducing.extend (toMvPowerSeries_denseInducing σ α)
      (MvPolynomial.aeval_on σ α R Y)
    map_one'  := by rw [← MvPolynomial.coe_one, DenseInducing.extend_eq
      (toMvPowerSeries_denseInducing σ α) (aeval_on_continuous σ α R Y), map_one]
    map_zero' := by
      simp only [← MvPolynomial.coe_zero]
      rw [DenseInducing.extend_eq (toMvPowerSeries_denseInducing σ α)
        (aeval_on_continuous σ α R Y), map_zero]
    map_mul'  := fun f g => by
      /- set p : (MvPowerSeries σ α) → (MvPowerSeries σ α) → Prop := fun f g =>
        DenseInducing.extend (toMvPowerSeries_denseInducing σ α) (⇑(aeval_on σ α R Y)) (f * g) =
          DenseInducing.extend (toMvPowerSeries_denseInducing σ α) (⇑(aeval_on σ α R Y)) f *
          DenseInducing.extend (toMvPowerSeries_denseInducing σ α) (⇑(aeval_on σ α R Y)) g with hp -/
      --simp only [AlgHom.mk_coe]
      apply @DenseRange.induction_on₂ (MvPolynomial σ α) (MvPowerSeries σ α) _
        (@MvPolynomial.toMvPowerSeries σ α _) _ (toMvPowerSeries_denseInducing σ α).dense _ _ f g
      · /- let τ := MvPowerSeries.topologicalSpace σ α
        have tg := @TopologicalRing.to_topologicalAddGroup _ _ τ (MvPowerSeries.topologicalRing σ α)
        rw [← isOpen_compl_iff]
        rw [isOpen_iff_mem_nhds]
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Prod.forall]
        intros a b hab
        rw [← add_zero (a, b), mem_nhds_add_iff, Prod.zero_eq_mk]  -/
        sorry
      · intro a b
        rw [← coe_mul]
        simp only [DenseInducing.extend_eq (toMvPowerSeries_denseInducing σ α)
          (aeval_on_continuous σ α _ _), map_mul]

    map_add'  := sorry
    commutes' := fun r => by
      have h : ((algebraMap α (MvPowerSeries σ α)) r) = ((algebraMap α (MvPolynomial σ α)) r) := by
        rw [MvPowerSeries.algebraMap_apply]
        rw [MvPolynomial.algebraMap_apply]
        simp only [Algebra.id.map_eq_id, RingHom.id_apply, coe_C]
      simp only [h, DenseInducing.extend_eq (toMvPowerSeries_denseInducing σ α)
        (aeval_on_continuous σ α _ _)]
      simp only [MvPolynomial.aeval_on, AlgHom.mk_coe, AlgHom.commutes] }
-/

theorem aeval_coe [DiscreteTopology α] : MvPowerSeries.aeval σ α R Y =
    DenseInducing.extend (toMvPowerSeries_denseInducing σ α) (MvPolynomial.aeval Y) := rfl

theorem aeval_continuous [DiscreteTopology α] : Continuous (aeval σ α R Y) := by
  rw [aeval_coe]
  apply DenseInducing.continuous_extend (toMvPowerSeries_denseInducing σ α)
  intro f
  use (aeval σ α R Y f)
  rw [tendsto_nhds]
  intros U hUopen hUf
  rw [Filter.mem_comap]
  use (aeval σ α R Y ⁻¹' U)
  constructor
  · rw [mem_nhds_iff]
    set S := MvPolynomial.toMvPowerSeries ⁻¹' ((aeval σ α R Y) ⁻¹' U)
    sorry
  · intro P hP
    rw [Set.mem_preimage, aeval_coe, Set.mem_preimage,
      DenseInducing.extend_eq _ (MvPolynomial.aeval_continuous σ α R Y)] at hP
    exact hP

theorem aeval_apply_X [DiscreteTopology α] (s : σ) :
    (aeval σ α R Y) (MvPowerSeries.X s) = Y s := by
  rw [aeval_coe, ← MvPolynomial.coe_X,
    DenseInducing.extend_eq _ (MvPolynomial.aeval_continuous _ _ _ _ ) (MvPolynomial.X s)]
  simp only [MvPolynomial.aeval, AlgHom.mk_coe, MvPolynomial.aeval_X]

variable {Y}

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - Existence -/
theorem exists_continuous_aeval [DiscreteTopology α] :
    ∃ (φ : MvPowerSeries σ α →ₐ[α] R) (_ : Continuous φ),
      ∀ (s : σ), φ (MvPowerSeries.X s) = Y s := by
  use aeval σ α R Y, aeval_continuous σ α R Y, fun s ↦ aeval_apply_X σ α R Y s

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - uniqueness -/
theorem continuous_aeval_unique [DiscreteTopology α] (φ : MvPowerSeries σ α →ₐ[α] R)
    (hφ : Continuous φ) (hφ' : ∀ (s : σ), φ (MvPowerSeries.X s) = Y s) (f : MvPowerSeries σ α) :
    φ f = aeval σ α R Y f := by
  set ψ := aeval σ α R Y
  have hφψ : ∀ (P : MvPolynomial σ α), φ P = ψ P := by
    intro P
    apply MvPolynomial.induction_on P _ _ _
    · intros a
      simp only [MvPolynomial.coe_C, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
    · intros f g hf hg
      rw [MvPolynomial.coe_add, map_add, map_add, hf, hg]
    · intros f n hf
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hf, hφ', aeval_apply_X]
  rw [← DenseInducing.extend_unique (toMvPowerSeries_denseInducing σ α) (fun P => rfl)
    (aeval_continuous σ α R _),
    ← DenseInducing.extend_unique (toMvPowerSeries_denseInducing σ α) hφψ hφ]

end MvPowerSeries

end foo
