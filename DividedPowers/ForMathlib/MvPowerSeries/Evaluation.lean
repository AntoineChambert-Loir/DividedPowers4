import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions
import Mathlib.Topology.Support
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Compacts
import Mathlib.RingTheory.MvPowerSeries.Basic
-- import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Data.Nat.Lattice

import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc
import DividedPowers.ForMathlib.Topology.LinearTopology
import DividedPowers.ForMathlib.MvPowerSeries.Topology
import DividedPowers.ForMathlib.Topology.Algebra.Algebra.Basic

/- # Evaluation of (multivariate) power series

Let `σ`, `R` `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `R` is a topological ring, and uniform add group,
and that `S` is a topological `R`-algebra, with a linear topology
(basis of neighborhoods of 0 consisting of ideals).

* `MvPowerSeries.eval₂` : Given `φ : R →+* S` and `a : σ → S`,
this file defines an evaluation of `f : MvPowerSeries σ R`,
that extends the evaluation of polynomials at `a`, by density,
provided `φ` and `a` satisfy certain conditions of which
the following lemmas assert the necessity

* `Continuous.on_scalars` : The map `φ` is continuous
* `Continuous.tendsto_apply_pow_zero_of_constantCoeff_zero` :
  for all `s : σ`, `(a s) ^ n` tends to 0 when `n` tends to infinity
* `Continuous.tendsto_apply_variables_zero_of_cofinite`:
  when `a s` tends to  zero for the filter of cofinite subsets of `σ`.

* `MvPowerSeries.continuous_eval₂` : continuity of the evaluation

* `MvPowerSeries.aeval` : the evaluation map as an algebra map

* `MvPowerSeries.continuous_aeval` : continuity of the evaluation

-/

section Evaluation

open MvPowerSeries MvPolynomial TopologicalSpace UniformSpace


variable (σ : Type*) [DecidableEq σ]
variable (R : Type*) [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S]  [TopologicalRing S]

local instance [TopologicalSpace R] : TopologicalSpace (MvPowerSeries σ R) :=
  topologicalSpace σ R

local instance [UniformSpace R] : UniformSpace (MvPowerSeries σ R) :=
  uniformSpace σ R

local instance [CommSemiring R] [TopologicalSpace R] :
    TopologicalSpace (MvPolynomial σ R) :=
  induced toMvPowerSeries Pi.topologicalSpace

local instance [CommSemiring R] [UniformSpace R] :
    UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

local instance : UniformSpace (MvPolynomial σ R) :=
  comap coeToMvPowerSeries.ringHom inferInstance

local instance : UniformAddGroup (MvPowerSeries σ R) :=
  Pi.instUniformAddGroup

local instance : UniformAddGroup (MvPolynomial σ R) :=
  UniformAddGroup.comap coeToMvPowerSeries.ringHom

local instance : TopologicalRing (MvPowerSeries σ R) :=
    MvPowerSeries.topologicalRing σ R

theorem Continuous.on_scalars
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε) :
    Continuous (ε.comp (C σ R)) := by
  simp only [RingHom.coe_comp]
  exact Continuous.comp hε MvPowerSeries.continuous_C

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (a) -/
theorem Continuous.tendsto_apply_pow_zero_of_constantCoeff_zero
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε) (s : σ) :
    Filter.Tendsto (fun n : ℕ => ε (MvPowerSeries.X s ^ n)) Filter.atTop (nhds 0) := by
  rw [← ε.map_zero]
  refine' Filter.Tendsto.comp hε.continuousAt (tendsto_pow_zero_of_constantCoeff_zero _)
  rw [MvPowerSeries.constantCoeff_X]

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (b) -/
theorem Continuous.tendsto_apply_variables_zero_of_cofinite
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε) :
    Filter.Tendsto (fun s : σ => ε (X s)) Filter.cofinite (nhds 0) := by
  rw [← ε.map_zero]
  exact Filter.Tendsto.comp hε.continuousAt variables_tendsto_zero

/-- Truncation of power series is continuous -/
theorem continuous_trunc'
    [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R] (n : σ →₀ ℕ) :
    Continuous (trunc' R n) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro m
  simp only [Function.comp_apply, coe_def, coeff_trunc']
  split_ifs with h
  · exact continuous_apply m
  · exact continuous_const

variable [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S][TopologicalRing S] [T2Space S] [CompleteSpace S]
variable (φ : R →+* S) (a : σ → S)

variable {σ R}

theorem MvPolynomial.coeToMvPowerSeries_denseRange :
    DenseRange (coeToMvPowerSeries.ringHom (R := R) (σ := σ)) := fun f => by
  rw [mem_closure_iff_nhds, nhds_pi]
  intro t
  rw [Filter.mem_pi]
  rintro ⟨I, hI, p, hp, hp_le⟩
  obtain ⟨n, hn⟩ := hI.bddAbove
  use f.truncFun' n
  constructor
  · apply hp_le
    simp only [Set.mem_pi]
    intro d hd
    apply mem_of_mem_nhds
    convert hp d using 2
    change MvPolynomial.coeff d (truncFun' n f)  = MvPowerSeries.coeff R d f
    rw [coeff_truncFun']
    rw [if_pos (hn hd)]
  · simp only [Set.mem_range, coeToMvPowerSeries.ringHom_apply, coe_inj, exists_eq]

variable
  [hS : LinearTopology S]
  (hpow : ∀ s, Filter.Tendsto (fun n : ℕ => (a s) ^ n) Filter.atTop (nhds 0))
  (hcof : Filter.Tendsto (fun s : σ => a s) Filter.cofinite (nhds 0))
  (hφ : Continuous φ)

/- The coercion of polynomials into power series is uniformly continuous. -/
theorem MvPolynomial.coeToMvPowerSeries_uniformContinuous :
    UniformContinuous (MvPolynomial.eval₂Hom φ a) := by
  apply uniformContinuous_of_continuousAt_zero
  intro u hu
  simp only [Filter.mem_map]
  rw [(induced_iff_nhds_eq _).mp rfl]
  simp only [map_zero, Filter.mem_comap]

  have : ∃ (I : Ideal S), ((I : Set S) ∈ nhds 0) ∧ I ≤ u := by
    have hS' := hS.isTopology
    rw [← Ideal.IsBasis.ofIdealBasis_topology_eq (Ideal.IsBasis.ofIdealBasis hS.toIdealBasis)] at hS'
    rw [map_zero, TopologicalSpace.ext_iff_nhds.mp hS', Ideal.IsBasis.mem_nhds_zero_iff] at hu
    rcases hu with ⟨i, hi⟩
    use ↑i
    convert hi
  rcases this with ⟨I, hI, hI'⟩

  simp only [Filter.tendsto_def] at hcof hpow
  specialize hcof I hI
  simp only [Filter.mem_cofinite] at hcof
  let hpow' := fun s ↦ hpow s I hI

  let n : σ → ℕ := fun s ↦ sInf {n : ℕ | (a s) ^ n.succ ∈ I}
  have hn_ne : ∀ s, Set.Nonempty {n : ℕ | (a s) ^ n.succ ∈ I} := fun s ↦ by
    specialize hpow' s
    simp only [Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at hpow'
    rcases hpow' with ⟨n, hn⟩
    use n
    simp only [Set.mem_setOf_eq]
    refine hn n.succ (Nat.le_succ n)
  have hn : Set.Finite (n.support) := by
    apply @Finite.Set.subset  _ _ _ hcof
    intro s
    simp only [Function.mem_support, ne_eq, Set.mem_compl_iff, Set.mem_preimage, SetLike.mem_coe, not_imp_comm, not_not]
    simp only [imp_or, n, Nat.sInf_eq_zero, Set.mem_setOf_eq, zero_add, pow_one, imp_self, true_or]
  let n₀ : σ →₀ ℕ := {
    toFun := n
    support := hn.toFinset
    mem_support_toFun := fun (s : σ) ↦  by simp }
  let D := Set.Iic n₀
  have hD : Set.Finite D := Set.finite_Iic _
  use Set.iInter (fun (d : D) ↦ { p | φ (p d.val) ∈ I})
  rw [nhds_pi, Filter.mem_pi]
  constructor
  · use D, hD
    use fun d ↦ if d ∈ D then φ ⁻¹' I else Set.univ
    constructor
    · intro d
      split_ifs with hd
      · apply hφ.continuousAt.preimage_mem_nhds
        erw [RingHom.map_zero]
        exact hI
      · exact Filter.univ_mem
    · intro p
      simp only [Set.mem_pi, Set.mem_ite_univ_right, Set.mem_preimage, SetLike.mem_coe,
        Set.iInter_coe_set, Set.mem_iInter]
      exact fun hp i hi ↦ hp i hi hi
  · intro p hp
    simp only [Set.iInter_coe_set, Set.mem_preimage, coeToMvPowerSeries.ringHom_apply,
      Set.mem_iInter, Set.mem_setOf_eq] at hp
    simp only [Set.mem_preimage]
    apply hI'
    simp only [coe_eval₂Hom, SetLike.mem_coe]
    rw [eval₂_eq]
    apply Ideal.sum_mem
    intro d _
    by_cases hd : d ∈ D
    · exact Ideal.mul_mem_right _ _ (hp d hd)
    · apply Ideal.mul_mem_left
      simp only [Set.mem_Iic, D, Finsupp.le_iff] at hd
      push_neg at hd
      rcases hd with ⟨s, hs', hs⟩
      rw [Finset.prod_eq_prod_diff_singleton_mul hs']
      · apply Ideal.mul_mem_left
        rw [← Nat.add_sub_of_le (Nat.succ_le_of_lt hs), pow_add]
        apply Ideal.mul_mem_right
        simp only [Finsupp.coe_mk, n₀, n]
        exact Nat.sInf_mem (hn_ne s)

theorem MvPolynomial.coeToMvPowerSeries_uniformInducing :
    UniformInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  ((uniformInducing_iff MvPolynomial.coeToMvPowerSeries.ringHom).mpr rfl)

theorem MvPolynomial.coeToMvPowerSeries_denseInducing :
    DenseInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  coeToMvPowerSeries_uniformInducing.denseInducing
    MvPolynomial.coeToMvPowerSeries_denseRange

noncomputable def MvPowerSeries.eval₂ :
    MvPowerSeries σ R →+* S :=
  DenseInducing.extendRingHom
    MvPolynomial.coeToMvPowerSeries_uniformInducing
    MvPolynomial.coeToMvPowerSeries_denseRange
    (MvPolynomial.coeToMvPowerSeries_uniformContinuous φ a hpow hcof hφ)

theorem MvPowerSeries.uniformContinuous_eval₂ :
    UniformContinuous (MvPowerSeries.eval₂ φ a hpow hcof hφ) :=
  uniformContinuous_uniformly_extend
    MvPolynomial.coeToMvPowerSeries_uniformInducing
    MvPolynomial.coeToMvPowerSeries_denseRange
    (MvPolynomial.coeToMvPowerSeries_uniformContinuous φ a hpow hcof hφ)

theorem MvPowerSeries.continuous_eval₂ :
    Continuous (MvPowerSeries.eval₂ φ a hpow hcof hφ) :=
  (MvPowerSeries.uniformContinuous_eval₂ φ a hpow hcof hφ).continuous

theorem MvPowerSeries.eval₂_coe (p : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a hpow hcof hφ p = MvPolynomial.eval₂ φ a p := by
  simp only [eval₂]
  apply DenseInducing.extend_eq
    MvPolynomial.coeToMvPowerSeries_denseInducing
    (MvPolynomial.coeToMvPowerSeries_uniformContinuous φ a hpow hcof hφ).continuous

theorem MvPowerSeries.eval₂_C (r : R) :
    MvPowerSeries.eval₂ φ a hpow hcof hφ (C σ R r) = φ r := by
  rw [← MvPolynomial.coe_C, eval₂_coe, MvPolynomial.eval₂_C]

theorem MvPowerSeries.eval₂_X (s : σ) :
    MvPowerSeries.eval₂ φ a hpow hcof hφ (X s) = a s := by
  rw [← MvPolynomial.coe_X, eval₂_coe, MvPolynomial.eval₂_X]

noncomputable def MvPowerSeries.aeval [TopologicalAlgebra R S] :
    MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂ (algebraMap R S) a hpow hcof TopologicalAlgebra.continuous_algebraMap
  commutes' := fun r ↦ by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [← MvPowerSeries.c_eq_algebraMap, eval₂_C]

end Evaluation
