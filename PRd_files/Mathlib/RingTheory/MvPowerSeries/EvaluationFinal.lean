/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.TopologicallyNilpotent
import Mathlib.Topology.Algebra.LinearTopology
import Mathlib.Topology.Algebra.UniformRing

/-! # Evaluation of multivariate power series

Let `σ`, `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `UniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : σ → S`, and `f : MvPowerSeries σ R`,
`MvPowerSeries.eval₂ f φ a` is the evaluation of the multivariate power series `f` at `a`.
It `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` satisfies two conditions
bundled in `MvPowerSeries.HasEval a` :
  - for all `s : σ`, `a s` is topologically nilpotent,
    meaning that `(a s) ^ n` tends to 0 when `n` tends to infinity
  - when `a s` tends to zero for the filter of cofinite subsets of `σ`.

Under `Continuous φ` and `HasEval a`, the following lemmas furnish the properties of evaluation:

* `MvPowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `MvPowerSeries.aeval`: the evaluation map as an algebra morphism
* `MvPowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `MvPowerSeries.continuous_eval₂`: continuity of the evaluation
* `MvPowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

-/

-- In PR #15019
namespace Ideal

-- PR'd to Mathlib/RingTheory/Ideal/Basic.lean
theorem prod_mem {α ι : Type*} [CommSemiring α] {f : ι → α} {s : Finset ι}
    (I : Ideal α) {i : ι} (hi : i ∈ s) (hfi : f i ∈ I) :
    ∏ i ∈ s, f i ∈ I := by
  classical
  rw [Finset.prod_eq_prod_diff_singleton_mul hi]
  exact Ideal.mul_mem_left _ _ hfi

end Ideal

namespace MvPowerSeries

open Topology

open Filter MvPolynomial RingHom Set TopologicalSpace UniformSpace

/- ## Necessary conditions -/

section

variable {σ : Type*}
variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable {S : Type*} [CommRing S] [TopologicalSpace S]
variable {φ : R →+* S}

-- We endow MvPowerSeries σ R with the Pi topology
open WithPiTopology

/-- Families at which power series can be consistently evaluated -/
structure HasEval (a : σ → S) : Prop where
  hpow : ∀ s, IsTopologicallyNilpotent (a s)
  tendsto_zero : Tendsto a cofinite (𝓝 0)

/-- The domain of evaluation of `MvPowerSeries`, as an ideal -/
def hasEvalIdeal [IsTopologicalRing S] [IsLinearTopology S S] : Ideal (σ → S) where
  carrier := {a | HasEval a}
  add_mem' {a} {b} ha hb := {
    hpow := fun s ↦ IsTopologicallyNilpotent.add (ha.hpow s) (hb.hpow s)
    tendsto_zero := by
      rw [← add_zero 0]
      exact ha.tendsto_zero.add hb.tendsto_zero }
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
      exact IsLinearTopology.tendsto_mul_zero_of_right _ _ (hx.hpow s)
    tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right _ _ hx.tendsto_zero }

theorem HasEval.add [IsTopologicalRing S] [IsLinearTopology S S]
    {a b : σ → S} (ha : HasEval a) (hb : HasEval b) : HasEval (a + b) :=
  hasEvalIdeal.add_mem' ha hb

theorem HasEval.zero [IsTopologicalRing S] [IsLinearTopology S S] : HasEval (0 : σ → S) :=
  hasEvalIdeal.zero_mem'

theorem HasEval.mul_left [IsTopologicalRing S] [IsLinearTopology S S]
    (c : σ → S) {x : σ → S} (hx : HasEval x) : HasEval (c * x) :=
  hasEvalIdeal.mul_mem_left c hx

theorem HasEval.mul_right [IsTopologicalRing S] [IsLinearTopology S S]
    (c : σ → S) {x : σ → S} (hx : HasEval x) : HasEval (x * c) :=
  hasEvalIdeal.mul_mem_right c hx

/-- [Bourbaki, *Algebra*, chap. 4, §4, n°3, Prop. 4 (i) (a & b)](bourbaki1981). -/
theorem HasEval.map (hφ : Continuous φ) {a : σ → R} (ha : HasEval a) :
    HasEval (fun s ↦ φ (a s)) where
  hpow := fun s ↦ IsTopologicallyNilpotent.map hφ (ha.hpow s)
  tendsto_zero := (map_zero φ ▸ hφ.tendsto 0).comp ha.tendsto_zero

protected theorem HasEval.X:
    HasEval (fun s ↦ (MvPowerSeries.X s : MvPowerSeries σ R)) where
  hpow := fun s ↦ tendsto_pow_zero_of_constantCoeff_zero (constantCoeff_X s)
  tendsto_zero := variables_tendsto_zero

/-- The inclusion of polynomials into power series has dense image -/
theorem _root_.MvPolynomial.coeToMvPowerSeries_denseRange :
    DenseRange (coeToMvPowerSeries.ringHom (R := R) (σ := σ)) := fun f => by
  have : Tendsto (fun d ↦ (trunc' R d f : MvPowerSeries σ R)) atTop (𝓝 f) := by
    rw [tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun n (hdn : d ≤ n) ↦ ?_
    simp [coeff_trunc', hdn]
  exact mem_closure_of_tendsto this <| .of_forall fun _ ↦ mem_range_self _

end

/- ## Construction of an evaluation morphism for power series -/

section Evaluation

open WithPiTopology

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R]
variable {S : Type*} [CommRing S] [UniformSpace S]
variable {φ : R →+* S}

-- We endow MvPowerSeries σ R with the product uniform structure
private instance : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

/-- The induced uniform structure of MvPolynomial σ R is an add group uniform structure -/
private instance [UniformAddGroup R] : UniformAddGroup (MvPolynomial σ R) :=
  UniformAddGroup.comap coeToMvPowerSeries.ringHom

theorem _root_.MvPolynomial.coeToMvPowerSeries_isUniformInducing :
    IsUniformInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  (isUniformInducing_iff ⇑coeToMvPowerSeries.ringHom).mpr rfl

theorem _root_.MvPolynomial.coeToMvPowerSeries_isDenseInducing :
    IsDenseInducing (coeToMvPowerSeries.ringHom (σ := σ) (R := R)) :=
  coeToMvPowerSeries_isUniformInducing.isDenseInducing coeToMvPowerSeries_denseRange

variable {a : σ → S}

/- The evaluation map on multivariate polynomials is uniformly continuous
for the uniform structure induced by that on multivariate power series. -/
theorem _root_.MvPolynomial.coeToMvPowerSeries_uniformContinuous
    [UniformAddGroup R] [UniformAddGroup S] [IsLinearTopology S S]
    (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (MvPolynomial.eval₂Hom φ a) := by
  apply uniformContinuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, IsLinearTopology.hasBasis_ideal.tendsto_right_iff]
  intro I hI
  let n : σ → ℕ := fun s ↦ sInf {n : ℕ | (a s) ^ n.succ ∈ I}
  have hn_ne : ∀ s, Set.Nonempty {n : ℕ | (a s) ^ n.succ ∈ I} := fun s ↦ by
    rcases ha.hpow s |>.eventually_mem hI |>.exists_forall_of_atTop with ⟨n, hn⟩
    use n
    simpa using hn n.succ n.le_succ
  have hn : Set.Finite (n.support) := by
    change n =ᶠ[cofinite] 0
    filter_upwards [ha.tendsto_zero.eventually_mem hI] with s has
    simpa [n, Pi.zero_apply, Nat.sInf_eq_zero, or_iff_left (hn_ne s).ne_empty] using has
  let n₀ : σ →₀ ℕ := .ofSupportFinite n hn
  let D := Iic n₀
  have hD : Set.Finite D := finite_Iic _
  have : ∀ d ∈ D, ∀ᶠ (p : MvPolynomial σ R) in 𝓝 0, φ (p.coeff d) ∈ I := fun d hd ↦ by
    have : Tendsto (φ ∘ coeff R d ∘ toMvPowerSeries) (𝓝 0) (𝓝 0) :=
      hφ.comp (continuous_coeff R d) |>.comp continuous_induced_dom |>.tendsto' 0 0 (map_zero _)
    filter_upwards [this.eventually_mem hI] with f hf
    simpa using hf
  rw [← hD.eventually_all] at this
  filter_upwards [this] with p hp
  rw [coe_eval₂Hom, SetLike.mem_coe, eval₂_eq]
  apply Ideal.sum_mem
  intro d _
  by_cases hd : d ∈ D
  · exact Ideal.mul_mem_right _ _ (hp d hd)
  · apply Ideal.mul_mem_left
    simp only [mem_Iic, D, Finsupp.le_iff] at hd
    push_neg at hd
    rcases hd with ⟨s, hs', hs⟩
    exact I.prod_mem hs' (I.pow_mem_of_pow_mem (Nat.sInf_mem (hn_ne s)) hs)

variable (φ a)
open scoped Classical in
/-- Evaluation of a multivariate power series at `f` at a point `a : σ → S`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion of a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `HasEval a`. -/
noncomputable def eval₂ (f : MvPowerSeries σ R) : S :=
  if H : ∃ p : MvPolynomial σ R, p = f then (MvPolynomial.eval₂ φ a H.choose)
  else IsDenseInducing.extend coeToMvPowerSeries_isDenseInducing (MvPolynomial.eval₂ φ a) f

theorem eval₂_coe (f : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a f = MvPolynomial.eval₂ φ a f := by
  have : ∃ p : MvPolynomial σ R, (p : MvPowerSeries σ R) = f := ⟨f, rfl⟩
  rw [eval₂, dif_pos this]
  congr
  rw [← MvPolynomial.coe_inj, this.choose_spec]

theorem eval₂_C (r : R) : eval₂ φ a (C σ R r) = φ r := by
  rw [← coe_C, eval₂_coe, MvPolynomial.eval₂_C]

theorem eval₂_X (s : σ) : eval₂ φ a (X s) = a s := by
  rw [← coe_X, eval₂_coe, MvPolynomial.eval₂_X]

variable [IsTopologicalSemiring R] [UniformAddGroup R]
    [UniformAddGroup S] [CompleteSpace S] [T2Space S]
    [IsTopologicalRing S] [IsLinearTopology S S]

variable {φ a}

/-- Evaluation of power series at adequate elements, as a `RingHom` -/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    MvPowerSeries σ R →+* S :=
  IsDenseInducing.extendRingHom
    coeToMvPowerSeries_isUniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem eval₂Hom_eq_extend (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    eval₂Hom hφ ha f =
      coeToMvPowerSeries_isDenseInducing.extend (MvPolynomial.eval₂ φ a) f :=
  rfl

theorem coe_eval₂Hom (hφ : Continuous φ) (ha : HasEval a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a := by
  ext f
  simp only [eval₂Hom_eq_extend, eval₂]
  split_ifs with h
  · obtain ⟨p, rfl⟩ := h
    simpa [MvPolynomial.coe_eval₂Hom, coeToMvPowerSeries.ringHom_apply] using
      coeToMvPowerSeries_isDenseInducing.extend_eq
        (coeToMvPowerSeries_uniformContinuous hφ ha).continuous p
  · rfl

-- Note: this is still true without the `T2Space` hypothesis, by arguing that the case
-- disjunction in the definition of `eval₂` only replaces some values by topologically
-- inseparable ones.
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    UniformContinuous (eval₂ φ a) := by
  rw [← coe_eval₂Hom hφ ha]
  exact uniformContinuous_uniformly_extend
    coeToMvPowerSeries_isUniformInducing
    coeToMvPowerSeries_denseRange
    (coeToMvPowerSeries_uniformContinuous hφ ha)

theorem continuous_eval₂ (hφ : Continuous φ) (ha : HasEval a) :
    Continuous (eval₂ φ a : MvPowerSeries σ R → S) :=
  (uniformContinuous_eval₂ hφ ha).continuous

theorem hasSum_eval₂ (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    HasSum
    (fun (d : σ →₀ ℕ) ↦ φ (coeff R d f) * (d.prod fun s e => (a s) ^ e))
    (MvPowerSeries.eval₂ φ a f) := by
  rw [← coe_eval₂Hom hφ ha, eval₂Hom_eq_extend hφ ha]
  convert (hasSum_of_monomials_self f).map (eval₂Hom hφ ha) (?_) with d
  · simp only [Function.comp_apply, coe_eval₂Hom, ← MvPolynomial.coe_monomial,
    eval₂_coe, eval₂_monomial]
  · rw [coe_eval₂Hom]; exact continuous_eval₂ hφ ha

theorem eval₂_eq_tsum (hφ : Continuous φ) (ha : HasEval a) (f : MvPowerSeries σ R) :
    MvPowerSeries.eval₂ φ a f =
      ∑' (d : σ →₀ ℕ), φ (coeff R d f) * (d.prod fun s e => (a s) ^ e) :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm

theorem eval₂_unique (hφ : Continuous φ) (ha : HasEval a)
    {ε : MvPowerSeries σ R → S} (hε : Continuous ε)
    (h : ∀ p : MvPolynomial σ R, ε p = MvPolynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  rw [← coe_eval₂Hom hφ ha]
  exact (coeToMvPowerSeries_isDenseInducing.extend_unique h hε).symm

theorem comp_eval₂ (hφ : Continuous φ) (ha : HasEval a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [UniformAddGroup T]
    {ε : S →+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε ∘ a) := by
  apply eval₂_unique _ (ha.map hε)
  · exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [Function.comp_apply, eval₂_coe]
    rw [← MvPolynomial.coe_eval₂Hom, ← comp_apply, MvPolynomial.comp_eval₂Hom,
      MvPolynomial.coe_eval₂Hom]
  · simp only [coe_comp, Continuous.comp hε hφ]

variable [Algebra R S] [ContinuousSMul R S]

/-- Evaluation of power series at adequate elements, as an `AlgHom` -/
noncomputable def aeval (ha : HasEval a) : MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂Hom (continuous_algebraMap R S) ha
  commutes' := fun r ↦ by
    simp only [toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [← c_eq_algebraMap, coe_eval₂Hom, eval₂_C]

theorem coe_aeval (ha : HasEval a) :
    ↑(aeval ha) = eval₂ (algebraMap R S) a := by
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]

theorem continuous_aeval (ha : HasEval a) :
    Continuous (aeval ha : MvPowerSeries σ R → S) := by
  rw [coe_aeval]
  exact continuous_eval₂ (continuous_algebraMap R S) ha

theorem aeval_coe (ha : HasEval a) (p : MvPolynomial σ R) :
    aeval ha (p : MvPowerSeries σ R) = p.aeval a := by
  rw [coe_aeval, aeval_def, eval₂_coe]

@[simp]
theorem aeval_unique {ε : MvPowerSeries σ R →ₐ[R] S} (hε : Continuous ε) :
    aeval (HasEval.X.map hε) = ε := by
  apply DFunLike.ext'
  rw [coe_aeval]
  refine (eval₂_unique (continuous_algebraMap R S) (HasEval.X.map hε) hε ?_).symm
  intro p
  change ε.comp (coeToMvPowerSeries.algHom R) p = _
  conv_lhs => rw [← p.aeval_X_left_apply, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def]
  simp [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def]

theorem hasSum_aeval (ha : HasEval a) (f : MvPowerSeries σ R) :
    HasSum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (d.prod fun s e => (a s) ^ e))
      (MvPowerSeries.aeval ha f) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

theorem aeval_eq_sum (ha : HasEval a) (f : MvPowerSeries σ R) :
    MvPowerSeries.aeval ha f =
      tsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (d.prod fun s e => (a s) ^ e)) :=
  (hasSum_aeval ha f).tsum_eq.symm

theorem comp_aeval (ha : HasEval a)
    {T : Type*} [CommRing T] [UniformSpace T] [UniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S →ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε)  := by
  apply DFunLike.ext'
  simp only [AlgHom.coe_comp, coe_aeval ha]
  erw [comp_eval₂ (continuous_algebraMap R S) ha hε, coe_aeval]
  congr!
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, RingHom.coe_coe]

end Evaluation

end MvPowerSeries
