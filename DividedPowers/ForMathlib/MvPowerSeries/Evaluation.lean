import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Constructions
import Mathlib.Topology.Support
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Sets.Compacts
import Mathlib.RingTheory.MvPowerSeries.Basic
-- import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Algebra.UniformRing
-- import Mathlib.Topology.Algebra.UniformGroup
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
and that `S` is a complete and separated topological `R`-algebra,
with `LinearTopology R`, which means there is a basis of neighborhoods of 0
consisting of ideals.

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

* `MvPowerSeries.eval₂_domain` : the `Prop`-valued structure
that is required to evaluate power series

* `MvPowerSeries.uniformContinuous_eval₂` : uniform continuity of the evaluation

* `MvPowerSeries.continuous_eval₂` : continuity of the evaluation

* `MvPowerSeries.aeval` : the evaluation map as an algebra map

-/

open MvPowerSeries MvPolynomial TopologicalSpace UniformSpace

section

/- ## Necessary conditions -/

variable {σ : Type*} [DecidableEq σ]
variable  {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [TopologicalSpace S] [TopologicalRing S]
variable  (φ : R →+* S) (hφ : Continuous φ)

/-- We endow MvPowerSeries σ R with the product topology -/
private instance : TopologicalSpace (MvPowerSeries σ R) := topologicalSpace σ R

/-- Families at which power series can be evaluated -/
structure MvPowerSeries.evalDomain (a : σ → S) : Prop where
  hpow : ∀ s, Filter.Tendsto (fun n : ℕ => (a s) ^ n) Filter.atTop (nhds 0)
  hcof : Filter.Tendsto a Filter.cofinite (nhds 0)

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (a & b) -/
theorem MvPowerSeries.map_evalDomain {a : σ → R} (ha : evalDomain a) :
    evalDomain (fun s ↦ φ (a s)) where
  hpow := fun s ↦  by
    simp_rw [← RingHom.map_pow]
    apply Filter.Tendsto.comp
    convert hφ.tendsto 0; rw [RingHom.map_zero]
    exact ha.hpow s
  hcof := by
    apply Filter.Tendsto.comp
    convert hφ.tendsto 0; rw [RingHom.map_zero]
    exact ha.hcof

theorem MvPowerSeries.evalDomain_X :
    evalDomain (fun s ↦ (MvPowerSeries.X s : MvPowerSeries σ R)) where
  hpow := fun s ↦ tendsto_pow_zero_of_constantCoeff_zero (constantCoeff_X s)
  hcof := variables_tendsto_zero

/-
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
-/


theorem Continuous.on_scalars
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε) :
    Continuous (ε.comp (C σ R)) := by
  simp only [RingHom.coe_comp]
  exact Continuous.comp hε MvPowerSeries.continuous_C

/-- The inclusion of polynomials into power series has dense image -/
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

end

section
/- ## Construction of an evaluation morphism for power series -/

variable {σ : Type*} [DecidableEq σ]
variable  {R : Type*} [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S][TopologicalRing S] [T2Space S] [CompleteSpace S]
variable  (φ : R →+* S) (hφ : Continuous φ)


-- local instance : TopologicalSpace (MvPowerSeries σ R) := topologicalSpace σ R

/-- We endow MvPowerSeries σ R with the product uniform structure
  (hence the product topology) -/
private instance : UniformSpace (MvPowerSeries σ R) := uniformSpace σ R

-- local instance : TopologicalSpace (MvPolynomial σ R) :=
--   induced toMvPowerSeries Pi.topologicalSpace

/-- The uniform structure of MvPowerSeries σ R is an add group uniform structure -/
private instance : UniformAddGroup (MvPowerSeries σ R) :=
  Pi.instUniformAddGroup

/-- We endow MvPolynomial σ R with the induced uniform structure (hence the induced topology) -/
private instance : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

/- local instance : UniformSpace (MvPolynomial σ R) :=
  comap coeToMvPowerSeries.ringHom inferInstance -/

/-- The induced uniform structure of MvPolynomial σ R is an add group uniform structure -/
private instance : UniformAddGroup (MvPolynomial σ R) :=
  UniformAddGroup.comap coeToMvPowerSeries.ringHom

/-- MvPowerSeries σ R is a topological ring -/
private instance : TopologicalRing (MvPowerSeries σ R) :=
    MvPowerSeries.topologicalRing σ R

variable {φ} [hS : LinearTopology S]
  {a : σ → S} (ha : MvPowerSeries.evalDomain a)

/- The coercion of polynomials into power series is uniformly continuous. -/
theorem MvPolynomial.coeToMvPowerSeries_uniformContinuous  :
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

  let hcof := ha.hcof
  let hpow := ha.hpow
  simp only [Filter.tendsto_def] at hcof hpow
  specialize hcof I hI
  simp only [Filter.mem_cofinite] at hcof
  let hpow := fun s ↦ hpow s I hI

  let n : σ → ℕ := fun s ↦ sInf {n : ℕ | (a s) ^ n.succ ∈ I}
  have hn_ne : ∀ s, Set.Nonempty {n : ℕ | (a s) ^ n.succ ∈ I} := fun s ↦ by
    specialize hpow s
    simp only [Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at hpow
    rcases hpow with ⟨n, hn⟩
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
  ((uniformInducing_iff coeToMvPowerSeries.ringHom).mpr rfl)

theorem MvPolynomial.coeToMvPowerSeries_denseInducing :
    DenseInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  coeToMvPowerSeries_uniformInducing.denseInducing
    coeToMvPowerSeries_denseRange

variable (φ a)
/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def MvPowerSeries.eval₂ :
    MvPowerSeries σ R → S :=
  DenseInducing.extend coeToMvPowerSeries_denseInducing (MvPolynomial.eval₂ φ a)

variable {φ a}
/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def MvPowerSeries.eval₂Hom :
    MvPowerSeries σ R →+* S :=
  DenseInducing.extendRingHom
    coeToMvPowerSeries_uniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem MvPowerSeries.coe_eval₂Hom :
    ⇑(MvPowerSeries.eval₂Hom hφ ha) = MvPowerSeries.eval₂ φ a := by
  rfl

theorem MvPowerSeries.uniformContinuous_eval₂ :
    UniformContinuous (MvPowerSeries.eval₂ φ a) :=
  uniformContinuous_uniformly_extend
    coeToMvPowerSeries_uniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem MvPowerSeries.continuous_eval₂ :
    Continuous (MvPowerSeries.eval₂ φ a) :=
  (MvPowerSeries.uniformContinuous_eval₂ hφ ha).continuous

theorem MvPowerSeries.eval₂_coe (p : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a p = MvPolynomial.eval₂ φ a p := by
  simp only [eval₂]
  apply DenseInducing.extend_eq
    coeToMvPowerSeries_denseInducing
    (coeToMvPowerSeries_uniformContinuous hφ ha).continuous

theorem MvPowerSeries.eval₂_C (r : R) :
    MvPowerSeries.eval₂ φ a (C σ R r) = φ r := by
  rw [← coe_C, eval₂_coe hφ ha, MvPolynomial.eval₂_C]

theorem MvPowerSeries.eval₂_X (s : σ) :
    MvPowerSeries.eval₂ φ a (X s) = a s := by
  rw [← coe_X, eval₂_coe hφ ha, MvPolynomial.eval₂_X]

theorem MvPowerSeries.eval₂_unique
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε)
    (h : ∀ p : MvPolynomial σ R, ε p = MvPolynomial.eval₂ φ a p) :
    ε = MvPowerSeries.eval₂ φ a := by
  apply symm
  unfold MvPowerSeries.eval₂
  exact DenseInducing.extend_unique _ h hε

/-- Evaluation of power series at adequate elements, as an `AlgHom` -/
noncomputable def MvPowerSeries.aeval [TopologicalAlgebra R S] :
    MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂Hom TopologicalAlgebra.continuous_algebraMap ha
  commutes' := fun r ↦ by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [← MvPowerSeries.c_eq_algebraMap, coe_eval₂Hom]
    exact eval₂_C TopologicalAlgebra.continuous_algebraMap ha r

theorem MvPowerSeries.coe_aeval [TopologicalAlgebra R S] :
    ⇑(MvPowerSeries.aeval ha) = MvPowerSeries.eval₂ (algebraMap R S) a :=
  rfl

theorem MvPowerSeries.aeval_unique [TopologicalAlgebra R S]
    (ε : MvPowerSeries σ R →ₐ[R] S) (hε : Continuous ε) :
    ε = MvPowerSeries.aeval (map_evalDomain ε hε MvPowerSeries.evalDomain_X) := by
  apply DFunLike.ext'
  rw [MvPowerSeries.coe_aeval]
  apply MvPowerSeries.eval₂_unique hε
  intro p
  induction p using MvPolynomial.induction_on with
  | h_C r =>
    simp only [AlgHom.toRingHom_eq_coe, coe_C, RingHom.coe_coe, MvPolynomial.eval₂_C]
    rw [MvPowerSeries.c_eq_algebraMap, AlgHom.commutes]
  | h_add p q hp hq =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp hq
    simp only [AlgHom.toRingHom_eq_coe, coe_add, map_add,
      RingHom.coe_coe, eval₂_add, hp, hq]
  | h_X p s h =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    simp only [AlgHom.toRingHom_eq_coe, coe_mul, coe_X, map_mul,
      RingHom.coe_coe, eval₂_mul, MvPolynomial.eval₂_X, h]

end
