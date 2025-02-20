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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Data.Nat.Lattice

import Mathlib.RingTheory.MvPowerSeries.Trunc
import DividedPowers.ForMathlib.Topology.LinearTopology
import DividedPowers.ForMathlib.MvPowerSeries.PiTopology
import Mathlib.Topology.Algebra.Algebra

-- In PR 15019


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

namespace MvPowerSeries

/- ## Necessary conditions -/

section

variable {n : ℕ} (hn : 1 < n)

example :  OrderedSemiring ℕ := by exact Nat.instOrderedSemiring

theorem test :  0 < n := lt_trans zero_lt_one hn

end

section

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommRing R] [TopologicalSpace R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [TopologicalSpace S] [TopologicalRing S]
variable {φ : R →+* S} (hφ : Continuous φ)

-- We endow MvPowerSeries σ R with the Pi topology
open WithPiTopology

def IsTopologicallyNilpotent
  {α : Type*} [Semiring α] [TopologicalSpace α] (a : α) : Prop :=
    Filter.Tendsto (fun n : ℕ => a ^ n) Filter.atTop (nhds 0)

namespace IsTopologicallyNilpotent

theorem map {α β : Type*} [CommRing α] [CommRing β] [TopologicalSpace α] [TopologicalSpace β]
  {φ : α →+* β} (hφ : Continuous φ) {a : α} (ha : IsTopologicallyNilpotent a) :
  IsTopologicallyNilpotent (φ a) := by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  apply Filter.Tendsto.comp _ ha
  convert hφ.tendsto 0; rw [map_zero]

theorem mul_right {α : Type*} [CommRing α] [TopologicalSpace α] [LinearTopology α] {a : α}
    (ha : IsTopologicallyNilpotent a) (b : α) : IsTopologicallyNilpotent (a * b) := by
  intro v hv
  rw [LinearTopology.mem_nhds_zero_iff] at hv
  rcases hv with ⟨I, _, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at ha ⊢
  rcases ha with ⟨n, ha⟩
  use n
  intro m hm
  rw [mul_pow]
  apply I_subset
  apply I.mul_mem_right _ (ha m hm)

 theorem mul_left {α : Type*} [CommRing α] [TopologicalSpace α] [LinearTopology α] (a : α) {b : α}
    (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a * b) := by
  rw [mul_comm]; exact mul_right hb a

theorem add {α : Type*} [CommRing α] [TopologicalSpace α] [LinearTopology α] {a b : α}
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) := by
  intro v hv
  rw [LinearTopology.mem_nhds_zero_iff] at hv
  rcases hv with ⟨I, _, I_mem_nhds, I_subset⟩
  specialize ha I_mem_nhds
  specialize hb I_mem_nhds
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le,
    Set.mem_preimage, SetLike.mem_coe] at ha hb
  rcases ha with ⟨na, ha⟩
  rcases hb with ⟨nb, hb⟩
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  use na + nb
  intro m hm
  apply I_subset
  apply I.add_pow_mem_of_pow_mem_of_le (ha na le_rfl) (hb nb le_rfl)
  apply le_trans hm (Nat.le_add_right _ _)

theorem zero {α : Type*} [CommRing α] [TopologicalSpace α] :
  IsTopologicallyNilpotent (0 : α) := tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])

end IsTopologicallyNilpotent

/-- Families at which power series can be evaluated -/
structure EvalDomain (a : σ → S) : Prop where
  hpow : ∀ s, IsTopologicallyNilpotent (a s)
  tendsto_zero : Filter.Tendsto a Filter.cofinite (nhds 0)

def EvalDomain_ideal [LinearTopology S] : Ideal (σ → S) where
  carrier := setOf EvalDomain
  add_mem' {a} {b} ha hb := {
    hpow := fun s ↦ IsTopologicallyNilpotent.add (ha.hpow s) (hb.hpow s)
    tendsto_zero := by
      rw [← add_zero 0]
      apply Filter.Tendsto.add ha.tendsto_zero hb.tendsto_zero }
  zero_mem' := {
    hpow := fun s ↦ by
      simp only [Pi.zero_apply]
      apply tendsto_atTop_of_eventually_const (i₀ := 1)
      intro i hi
      rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)]
    tendsto_zero := tendsto_const_nhds }
  smul_mem' c {x} hx := {
    hpow := fun s ↦ by
      simp only [IsTopologicallyNilpotent, Pi.smul_apply', smul_eq_mul, mul_pow]
      exact LinearTopology.tendsto_zero_mul _ _ _ (hx.hpow s)
    tendsto_zero := LinearTopology.tendsto_zero_mul _ _ _ hx.tendsto_zero }

--set_option linter.unusedSectionVars false
omit [DecidableEq σ] [TopologicalRing R] [TopologicalRing S] in
/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (a & b) -/
theorem EvalDomain.map {a : σ → R} (ha : EvalDomain a) (hφ : Continuous φ) :
    EvalDomain (fun s ↦ φ (a s)) where
  hpow := fun s ↦ IsTopologicallyNilpotent.map hφ (ha.hpow s)
  tendsto_zero := by
    apply Filter.Tendsto.comp
    convert hφ.tendsto 0; rw [RingHom.map_zero]
    exact ha.tendsto_zero

omit [TopologicalRing R] in
theorem EvalDomain.evalDomain_X :
    EvalDomain (fun s ↦ (MvPowerSeries.X s : MvPowerSeries σ R)) where
  hpow := fun s ↦ tendsto_pow_zero_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := variables_tendsto_zero

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

omit [TopologicalRing S] in
theorem Continuous.on_scalars
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε) :
    Continuous (ε.comp (C σ R)) := by
  simp only [RingHom.coe_comp]
  exact Continuous.comp hε MvPowerSeries.continuous_C

omit [DecidableEq σ] [TopologicalRing R] in
/-- The inclusion of polynomials into power series has dense image -/
theorem _root_.MvPolynomial.coeToMvPowerSeries_denseRange :
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


/- ## Construction of an evaluation morphism for power series -/

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S][TopologicalRing S] [T2Space S] [CompleteSpace S]
variable {φ : R →+* S} (hφ : Continuous φ)


-- We endow MvPowerSeries σ R with the product uniform structure
open WithPiUniformity

private instance : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

/-- The induced uniform structure of MvPolynomial σ R is an add group uniform structure -/
private instance : UniformAddGroup (MvPolynomial σ R) :=
  UniformAddGroup.comap coeToMvPowerSeries.ringHom


/- -- local instance : TopologicalSpace (MvPolynomial σ R) :=
--   induced toMvPowerSeries Pi.topologicalSpace

/-- The uniform structure of MvPowerSeries σ R is an add group uniform structure -/
private instance : UniformAddGroup (MvPowerSeries σ R) :=
  Pi.instUniformAddGroup

/-- We endow MvPolynomial σ R with the induced uniform structure (hence the induced topology) -/

/- local instance : UniformSpace (MvPolynomial σ R) :=
  comap coeToMvPowerSeries.ringHom inferInstance -/

/-- MvPowerSeries σ R is a topological ring -/
private instance : TopologicalRing (MvPowerSeries σ R) :=
    MvPowerSeries.topologicalRing σ R
-/

variable [hS : LinearTopology S]
  {a : σ → S} (ha : EvalDomain a)

-- NOTE: ha and hφ do not get picked up automatically.
omit [TopologicalRing R] [TopologicalRing S] [T2Space S] [CompleteSpace S] in
/- The coercion of polynomials into power series is uniformly continuous. -/
theorem _root_.MvPolynomial.coeToMvPowerSeries_uniformContinuous (hφ : Continuous φ)
    (ha : EvalDomain a) : UniformContinuous (MvPolynomial.eval₂Hom φ a) := by
  apply uniformContinuous_of_continuousAt_zero
  intro u hu
  simp only [coe_eval₂Hom, (induced_iff_nhds_eq _).mp rfl, coe_zero,
    Filter.mem_map, Filter.mem_comap]
  rw [map_zero, hS.mem_nhds_zero_iff] at hu
  rcases hu with ⟨I, _, hI, hI'⟩
  let tendsto_zero := ha.tendsto_zero
  let hpow := ha.hpow
  simp only [Filter.tendsto_def] at tendsto_zero hpow
  specialize tendsto_zero I hI
  simp only [Filter.mem_cofinite] at tendsto_zero
  let hpow' := fun s ↦ hpow s hI
  simp only [Filter.mem_map, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage, SetLike.mem_coe] at hpow'

  let n : σ → ℕ := fun s ↦ sInf {n : ℕ | (a s) ^ n.succ ∈ I}
  have hn_ne : ∀ s, Set.Nonempty {n : ℕ | (a s) ^ n.succ ∈ I} := fun s ↦ by
    rcases hpow' s with ⟨n, hn⟩
    use n
    simp only [Set.mem_setOf_eq]
    refine hn n.succ (Nat.le_succ n)
  have hn : Set.Finite (n.support) := by
    apply @Finite.Set.subset  _ _ _ tendsto_zero
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

omit [DecidableEq σ] [UniformAddGroup R] [TopologicalRing R] in
theorem _root_.MvPolynomial.coeToMvPowerSeries_uniformInducing :
    UniformInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  ((uniformInducing_iff coeToMvPowerSeries.ringHom).mpr rfl)

omit [DecidableEq σ] [UniformAddGroup R] [TopologicalRing R] in
theorem _root_.MvPolynomial.coeToMvPowerSeries_denseInducing :
    DenseInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  coeToMvPowerSeries_uniformInducing.denseInducing
    coeToMvPowerSeries_denseRange

variable (φ a)
/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def eval₂ : MvPowerSeries σ R → S :=
  DenseInducing.extend coeToMvPowerSeries_denseInducing (MvPolynomial.eval₂ φ a)


/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def eval₂' (f : MvPowerSeries σ R) :
    S := by
  let hp := fun (p : MvPolynomial σ R) ↦ p = f
  classical
  exact if (Classical.epsilon hp = f) then (MvPolynomial.eval₂ φ a (Classical.epsilon hp))
    else DenseInducing.extend coeToMvPowerSeries_denseInducing (MvPolynomial.eval₂ φ a) f

variable {φ a}
/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def eval₂Hom (hφ : Continuous φ) :
    MvPowerSeries σ R →+* S :=
  DenseInducing.extendRingHom
    coeToMvPowerSeries_uniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem coe_eval₂Hom (hφ : Continuous φ) :
    ⇑(eval₂Hom ha hφ) = eval₂ φ a := by
  rfl

omit [TopologicalRing R] [TopologicalRing S] [T2Space S] in
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : EvalDomain a) :
    UniformContinuous (eval₂ φ a) :=
  uniformContinuous_uniformly_extend
    coeToMvPowerSeries_uniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

omit [TopologicalRing R] [TopologicalRing S] [T2Space S] in
theorem continuous_eval₂ (hφ : Continuous φ) (ha : EvalDomain a) :
    Continuous (eval₂ φ a : MvPowerSeries σ R → S) :=
  (uniformContinuous_eval₂ hφ ha).continuous

omit [TopologicalRing R] [TopologicalRing S] [CompleteSpace S] in
theorem eval₂_coe (p : MvPolynomial σ R) (hφ : Continuous φ) (ha : EvalDomain a) :
    MvPowerSeries.eval₂ φ a p = MvPolynomial.eval₂ φ a p := by
  simp only [eval₂]
  apply DenseInducing.extend_eq
    coeToMvPowerSeries_denseInducing
    (coeToMvPowerSeries_uniformContinuous hφ ha).continuous

omit [DecidableEq
  σ] [UniformAddGroup
  R] [TopologicalRing R] [UniformAddGroup S] [TopologicalRing S] [T2Space S] [CompleteSpace S] hS in
theorem eval₂'_coe (f : MvPolynomial σ R) :
    MvPowerSeries.eval₂' φ a f = MvPolynomial.eval₂ φ a f := by
  have hf : (Classical.epsilon fun (p : MvPolynomial σ R) ↦ p = (f : MvPowerSeries σ R)) =
      (f : MvPowerSeries σ R) := by
    apply Classical.epsilon_spec (p := fun (p : MvPolynomial σ R) ↦
      p = (f : MvPowerSeries σ R))
    use f
  simp only [eval₂']
  rw [if_pos hf]
  apply congr_arg
  rw [← MvPolynomial.coe_inj, hf]

set_option linter.unusedSectionVars false
theorem eval₂_C (r : R) (hφ : Continuous φ) (ha : EvalDomain a)  :
    eval₂ φ a (C σ R r) = φ r := by
  rw [← coe_C, eval₂_coe _ hφ ha, MvPolynomial.eval₂_C]

theorem eval₂'_C (r : R)  :
    eval₂' φ a (C σ R r) = φ r := by
  rw [← coe_C, eval₂'_coe, MvPolynomial.eval₂_C]

theorem eval₂_X (s : σ) (hφ : Continuous φ) (ha : EvalDomain a) :
    eval₂ φ a (X s) = a s := by
  rw [← coe_X, eval₂_coe _ hφ ha, MvPolynomial.eval₂_X]

theorem eval₂'_X (s : σ) :
    eval₂' φ a (X s) = a s := by
  rw [← coe_X, eval₂'_coe, MvPolynomial.eval₂_X]

variable (f : MvPowerSeries σ R) (d : σ →₀ ℕ)

theorem hasSum_eval₂ (f : MvPowerSeries σ R) :
    HasSum
    (fun (d : σ →₀ ℕ) ↦ φ (coeff R d f) * (d.prod fun s e => (a s) ^ e))
    (MvPowerSeries.eval₂ φ a f) := by
  convert (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (continuous_eval₂ hφ ha) with d
  simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial, eval₂_coe hφ ha, eval₂_monomial]

theorem eval₂_eq_sum (f : MvPowerSeries σ R) :
    MvPowerSeries.eval₂ φ a f =
      tsum (fun (d : σ →₀ ℕ) ↦ φ (coeff R d f) * (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm

theorem eval₂_unique
    {ε : MvPowerSeries σ R →+* S} (hε : Continuous ε)
    (h : ∀ p : MvPolynomial σ R, ε p = MvPolynomial.eval₂ φ a p) :
    ε = eval₂ φ a :=
  (DenseInducing.extend_unique _ h hε).symm

theorem comp_eval₂
    {T : Type*} [CommRing T] [UniformSpace T] [LinearTopology T] [T2Space T]
    {ε : S →+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε ∘ a) := by
  rw [← coe_eval₂Hom hφ ha, ← RingHom.coe_comp]
  apply eval₂_unique
  simp only [RingHom.coe_comp]
  exact Continuous.comp hε (continuous_eval₂ hφ ha)
  intro p
  simp only [RingHom.coe_comp, Function.comp_apply, eval₂_coe]
  rw [coe_eval₂Hom hφ ha, eval₂_coe hφ ha, ← MvPolynomial.coe_eval₂Hom]
  rw [← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rfl

variable [Algebra R S] [ContinuousSMul R S]

/-- Evaluation of power series at adequate elements, as an `AlgHom` -/
noncomputable def aeval : MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' := fun r ↦ by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [← c_eq_algebraMap, coe_eval₂Hom]
    exact eval₂_C (continuous_algebraMap R S) ha r

theorem coe_aeval :
    ⇑(MvPowerSeries.aeval ha) = MvPowerSeries.eval₂ (algebraMap R S) a :=
  rfl

theorem continuous_aeval : Continuous (aeval ha : MvPowerSeries σ R → S) :=
  continuous_eval₂ (continuous_algebraMap R S) ha

theorem aeval_coe (p : MvPolynomial σ R) :
    MvPowerSeries.aeval ha (p : MvPowerSeries σ R) = MvPolynomial.aeval a p := by
  simp only [coe_aeval, eval₂_coe (continuous_algebraMap R S) ha, aeval_def]

theorem aeval_unique {ε : MvPowerSeries σ R →ₐ[R] S} (hε : Continuous ε) :
    ε = aeval (EvalDomain.evalDomain_X.map hε) := by
  apply DFunLike.ext'
  rw [coe_aeval]
  apply eval₂_unique hε
  intro p
  induction p using MvPolynomial.induction_on with
  | h_C r =>
    simp only [AlgHom.toRingHom_eq_coe, coe_C, RingHom.coe_coe, MvPolynomial.eval₂_C]
    rw [c_eq_algebraMap, AlgHom.commutes]
  | h_add p q hp hq =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp hq
    simp only [AlgHom.toRingHom_eq_coe, coe_add, map_add,
      RingHom.coe_coe, eval₂_add, hp, hq]
  | h_X p s h =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    simp only [AlgHom.toRingHom_eq_coe, coe_mul, coe_X, map_mul,
      RingHom.coe_coe, eval₂_mul, MvPolynomial.eval₂_X, h]

theorem hasSum_aeval (f : MvPowerSeries σ R) :
    HasSum
    (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (d.prod fun s e => (a s) ^ e))
    (MvPowerSeries.aeval ha f)
     :=  by
  have := hasSum_eval₂ (continuous_algebraMap R S) ha f
  simp_rw [← smul_eq_mul, algebraMap_smul] at this
  rw [coe_aeval]
  exact this

theorem aeval_eq_sum (f : MvPowerSeries σ R) :
    MvPowerSeries.aeval ha f =
      tsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_aeval ha f).tsum_eq.symm

theorem comp_aeval
    {T : Type*} [CommRing T] [UniformSpace T] [UniformAddGroup T]
    [LinearTopology T] [T2Space T] [TopologicalRing T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S →ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε)  := by
  apply DFunLike.coe_injective
  simp only [AlgHom.coe_comp, -- AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    coe_aeval ha]
  erw [comp_eval₂ (continuous_algebraMap R S) ha hε]
  apply congr_arg₂
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ext; rfl

end MvPowerSeries

namespace PowerSeries

/- take f : PowerSeries R = MvPowerSeries Unit R
evaluate at s : S  =~= Unit → S

def
-/

variable {R : Type*} [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S][TopologicalRing S]
  [T2Space S] [CompleteSpace S]

/-- Families at which power series can be evaluated -/
structure EvalDomain (a : S) : Prop where
  hpow : IsTopologicallyNilpotent a

open WithPiUniformity

def EvalDomain.ideal [LinearTopology S] : Ideal S where
  carrier   := setOf IsTopologicallyNilpotent
  add_mem'  := IsTopologicallyNilpotent.add
  zero_mem' := IsTopologicallyNilpotent.zero
  smul_mem' := IsTopologicallyNilpotent.mul_left

variable {φ : R →+* S} (hφ : Continuous φ) (a : S)

noncomputable def eval₂ : PowerSeries R → S :=
  MvPowerSeries.eval₂ φ (fun _ ↦ a)

variable [hS : LinearTopology S] {a : S} (ha : EvalDomain a)

def EvalDomain.const : MvPowerSeries.EvalDomain (fun (_ : Unit) ↦ a) where
  hpow := fun _ ↦ ha.hpow
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

noncomputable def eval₂Hom : PowerSeries R →+* S :=
  MvPowerSeries.eval₂Hom hφ ha.const

variable [Algebra R S] [ContinuousSMul R S]

noncomputable def aeval : PowerSeries R →ₐ[R] S :=
  MvPowerSeries.aeval ha.const

end PowerSeries
