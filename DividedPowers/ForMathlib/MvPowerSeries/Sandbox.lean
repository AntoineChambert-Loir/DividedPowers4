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

-- import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology
-- import Mathlib.Topology.Algebra.Algebra
-- import Mathlib.Data.MvPolynomial.CommRing
-- import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc

/- Attempt to understand topologies on polynomials and power series,
in order to have “easy” evaluations of power series.
-/

section CompactOpenTopology

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

-- #synth TopologicalSpace (C(X, Y))
-- ContinuousMap.compactOpen

end CompactOpenTopology

section CompactSupport

open TopologicalSpace ContinuousMap

variable (X : Type*) [TopologicalSpace X] (S : Set X) (K : Compacts X)
  (Y : Type*) [TopologicalSpace Y] [Zero Y]

variable {X}
def ContinuousMapWithSupport := { f : C(X, Y) // tsupport f ≤ S }

notation:9000 "C(" X ", " Y " | " S ")" => ContinuousMapWithSupport (X := X) S Y

def TopologicalSpace.continuousMapWithSupport :
    TopologicalSpace (C(X, Y | S))  := induced Subtype.val compactOpen

variable (X)
def ContinuousMapWithCompactSupport := { f : C(X, Y) // HasCompactSupport f }

notation:9000 "Cₖ(" X ", " Y ")"=> ContinuousMapWithCompactSupport X Y

variable {X}
def toContinuousMapWithCompactSupport (f : C(X, Y | K)) : Cₖ(X, Y) :=
  ⟨f.val,
   IsCompact.of_isClosed_subset K.isCompact (isClosed_tsupport _) f.prop⟩

variable {Y}
def TopologicalSpace.continuousMapWithCompactSupport :
    TopologicalSpace (Cₖ(X, Y)) :=
  iSup (fun K ↦ coinduced (toContinuousMapWithCompactSupport K _) (continuousMapWithSupport _ _))

local instance : TopologicalSpace Cₖ(X, Y) := continuousMapWithCompactSupport

local instance (S : Set X) : TopologicalSpace C(X, Y | S) := continuousMapWithSupport S Y

/- The universal property of the topology of `Cₖ(X, Y) -/
example
    (Z : Type*) [TopologicalSpace Z] (T : Cₖ(X, Y) → Z) :
    Continuous T ↔ ∀ (K : Compacts X),
      Continuous (T ∘ (toContinuousMapWithCompactSupport K Y)) := by
  constructor
  · intro hT K
    apply Continuous.comp hT
    apply continuous_iSup_rng (i := K)
    rw [continuous_iff_coinduced_le]
    exact le_rfl
  · intro hT
    rw [continuous_iSup_dom]
    intro K
    simp only [continuous_iff_coinduced_le, coinduced_compose]
    rw [← continuous_iff_coinduced_le]
    exact hT K

example (X : Type*) [TopologicalSpace X]
    (F K : Set X) (hF : IsClosed F) (hK : IsCompact K) (hFK : F ≤ K) :
    IsCompact F := IsCompact.of_isClosed_subset hK hF hFK

end CompactSupport

section Uniform
/- Structure uniforme produit -/

variable (ι : Type*) (X : ι → Type*) [(i : ι) → UniformSpace (X i)]

example : UniformSpace (Π i, X i) := Pi.uniformSpace fun i => X i

example : TopologicalSpace (Π i, X i) := Pi.topologicalSpace

end Uniform

section Algebra

open MvPowerSeries MvPolynomial TopologicalSpace UniformSpace

/- Let `σ` and `R` by types, with `CommRing R` if necessary.

`MvPowerSeries σ R` is a pi-type. If `R` has a topology or a uniform structure,
then that for `R` is clear.

-/

variable (σ R : Type*) [DecidableEq σ] [CommRing R]

def MvPowerSeries.topologicalSpace [TopologicalSpace R] :
    TopologicalSpace (MvPowerSeries σ R) := Pi.topologicalSpace

def MvPowerSeries.uniformSpace [UniformSpace R] :
    UniformSpace (MvPowerSeries σ R) := Pi.uniformSpace _

/- The case of polynomials is less clear.

On can of course endow it with the induced topology and the induced uniformity.
-/

example [TopologicalSpace R] : TopologicalSpace (MvPolynomial σ R) :=
  induced toMvPowerSeries Pi.topologicalSpace

example [UniformSpace R] : UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

/-
but since  polynomials correspond to finitely supported functions,
it might be more natural to give them the inductive limit topology.

Inded, with the induced topology, polynomials `P n` may converge to `0`,
but `eval 1 (P n) = 1` for all `n`.
For example, `P n = T ^ n`. (And `eval 2 P n ` does not converge…)

A set `s : Set (MvPolynomial σ R)` is open if and only if its traces
`Set ({p : MvPolynomial σ R // support p ≤ D})` are open.
At each level, this can be viewed as the compact open topology,
but since the source is discrete, this is the product topology.
The corresponding uniformity is the compact convergence.

Anyway…

-/

section MvPowerSeries_aeval

/-  So now, we will try to extend evaluation of polynomials to power series

We want to define
`MvPowerSeries σ R →+* S`
associated with `a : σ → S` which satisfies the reasonable assumptions
given in Bourbaki, Algèbre, 4…
In particular, `S` is a complete linearly topologized ring,
`(a s) ^ n → 0` for all `s`, and `a s → 0`, when `s` goes to infinity.

DenseInducing.extendRingHom.{u_3, u_2, u_1}
  {α : Type u_1} [inst✝ : UniformSpace α] [inst✝¹ : Semiring α]
  {β : Type u_2} [inst✝² : UniformSpace β] [inst✝³ : Semiring β] [inst✝⁴ : TopologicalSemiring β]
  {γ : Type u_3} [inst✝⁵ : UniformSpace γ] [inst✝⁶ : Semiring γ] [inst✝⁷ : TopologicalSemiring γ] [inst✝⁸ : T2Space γ] [inst✝⁹ : CompleteSpace γ]
  {i : α →+* β}
  {f : α →+* γ}
  (ue : UniformInducing ⇑i)
  (dr : DenseRange ⇑i)
  (hf : UniformContinuous ⇑f) : β →+* γ

so β := MvPowerSeries σ R
   γ := S
   α := MvPolynomial σ R
-/

variable {σ : Type*} [DecidableEq σ]
variable {R : Type*} -- [CommRing R] [UniformSpace R] [TopologicalRing R]

local instance [TopologicalSpace R] : TopologicalSpace (MvPowerSeries σ R) :=
  MvPowerSeries.topologicalSpace σ R

local instance [UniformSpace R] : UniformSpace (MvPowerSeries σ R) :=
  MvPowerSeries.uniformSpace σ R

local instance [CommSemiring R] [TopologicalSpace R] :
    TopologicalSpace (MvPolynomial σ R) :=
  induced toMvPowerSeries Pi.topologicalSpace

local instance [CommSemiring R] [UniformSpace R] :
    UniformSpace (MvPolynomial σ R) :=
  comap toMvPowerSeries (Pi.uniformSpace _)

/- The next lemma is not so difficult but hard to spell out.
  For the multiplication, the point is that a given coefficient of the
  product of two power series f and g is given by a polynomial in
  finitely many coefficients of f and g (see `trunc'_mul`), hence is continuous.
  (This also shows that Laurent series will only form a topological semiring
  if one brings in a compact support condition on the negative part.)
  When `R` is a ring with the discrete topology,
  there is the stronger result that this topology is generated by ideals.

  So 1) prove that trunc' is continuous
     2) use that multiplication is continuous on polynomials -/

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

/-- Power series over a topological commutative semiring form a topological semiring -/
def MvPowerSeries.topologicalSemiring
    [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R] :
    TopologicalSemiring (MvPowerSeries σ R) where
  continuous_add := Pi.continuousAdd.continuous_add
  continuous_mul := continuous_pi fun i => by
    classical
    have : (fun (f : MvPowerSeries σ R × MvPowerSeries σ R) => (f.1 * f.2) i) = (fun f => MvPowerSeries.coeff R i (f.1 * f.2)) := by ext; rfl
    simp_rw [this, MvPowerSeries.coeff_mul]
    apply continuous_finset_sum
    rintro ⟨j, k⟩ _
    dsimp only
    have : (fun (f : MvPowerSeries σ R × MvPowerSeries σ R) ↦ (coeff R j f.1) * (coeff R k f.2)) =
      (fun (u : R × R) ↦ u.1 * u.2) ∘ (fun f ↦ ⟨coeff R j f.1, coeff R k f.2⟩) := by ext; rfl
    rw [this]
    apply Continuous.comp continuous_mul
    exact Continuous.prod_map (continuous_apply j) (continuous_apply k)

/-- Power series over a topological commutative ring form a topological ring -/
def MvPowerSeries.topologicalRing
    [CommRing R] [TopologicalSpace R] [TopologicalRing R] :
    TopologicalRing (MvPowerSeries σ R) where
  toTopologicalSemiring := MvPowerSeries.topologicalSemiring
  continuous_neg := Pi.continuousNeg.continuous_neg

variable [CommRing R] [UniformSpace R] [UniformAddGroup R] [TopologicalRing R]
variable {S : Type*} [CommRing S] [UniformSpace S] [UniformAddGroup S][TopologicalRing S] [T2Space S] [CompleteSpace S]
variable (φ : R →+* S) (a : σ → S)

def i : MvPolynomial σ R →+* MvPowerSeries σ R := MvPolynomial.coeToMvPowerSeries.ringHom

def f : MvPolynomial σ R →+* S := MvPolynomial.eval₂Hom φ a

local instance : UniformSpace (MvPolynomial σ R) :=
  comap coeToMvPowerSeries.ringHom inferInstance

local instance : UniformAddGroup (MvPowerSeries σ R) :=
  Pi.instUniformAddGroup

local instance : UniformAddGroup (MvPolynomial σ R) :=
  UniformAddGroup.comap coeToMvPowerSeries.ringHom

theorem dr : DenseRange (i (R := R) (σ := σ)) := fun f => by
  rw [mem_closure_iff_nhds, nhds_pi]
  intro t
  rw [Filter.mem_pi]
  rintro ⟨I, hI, p, hp, hp_le⟩
  obtain ⟨n, hn⟩ := hI.bddAbove
  simp only [i]
  use f.truncFun' n
  constructor
  · apply hp_le
    simp only [Set.mem_pi]
    intro d hd
    apply mem_of_mem_nhds
    convert hp d using 2
    change MvPolynomial.coeff d (truncFun' n f)  = coeff R d f
    rw [coeff_truncFun']
    rw [if_pos (hn hd)]
  · simp only [Set.mem_range, coeToMvPowerSeries.ringHom_apply, coe_inj, exists_eq]

theorem ue : UniformInducing (i (R := R) (σ := σ)) :=
  (uniformInducing_iff ⇑i).mpr rfl

example (X Y : Type*) (f : X → Y) (s t : Set Y) (hst : s ⊆ t): f ⁻¹' s ⊆ f ⁻¹' t :=
  Set.preimage_mono hst

example (I : Ideal S) (a : S) : Set ℕ := {n | a ^ n ∈ I}
noncomputable example (I : Ideal S) (a : S) : ℕ := sInf {n | a ^ n ∈ I}

variable
  [hS : LinearTopology S]
  (hpow : ∀ s, Filter.Tendsto (fun n : ℕ => (a s) ^ n) Filter.atTop (nhds 0))
  (hcof : Filter.Tendsto (fun s : σ => a s) Filter.cofinite (nhds 0))
  (hφ : Continuous φ)

/- This is the crucial part of the proof, where one uses that the family `a`
  satisfies the conditions and `S` is linearly topologized -/
theorem hf : UniformContinuous (f φ a) := by
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
    simp only [f, coe_eval₂Hom, SetLike.mem_coe]
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

    /- p = ∑ c m T ^m
      f φ a p = ∑ φ (c m) a ^ m
      * case of one indeterminate
        take n so that a ^ n ∈ I (possible, by hpow)
        require phi (c m) ∈ I for all m < n
      * case of finitely many indeterminates
        take n s : ℕ, minimal, so that (a s) ^ (n s + 1) ∈ I for all s (possible, by hpow)
        require phi(c m) ∈ I for all (the finitely many) m such that m < n
      * general case
        choose (n s) as above
        by hcof, there is only a finite set of s such that a s ∉ I
        so n s = 0 outside of this finite set : n is finitely supported
        then require phi(c m) ∈ I for all the finitely many m such that m < n



  sorry -/

local instance [TopologicalSpace R] [TopologicalSemiring R] :
    TopologicalSemiring (MvPowerSeries σ R) := MvPowerSeries.topologicalSemiring

noncomputable def MvPowerSeries.eval₂ :
    MvPowerSeries σ R →+* S :=
  DenseInducing.extendRingHom ue dr (hf φ a hpow hcof hφ)

theorem MvPowerSeries.eval₂_coe (p : MvPolynomial σ R) :
    MvPowerSeries.eval₂ φ a hpow hcof hφ p = MvPolynomial.eval₂ φ a p := by
  simp only [eval₂]
  exact DenseInducing.extend_eq (ue.denseInducing dr) (hf φ a hpow hcof hφ).continuous p

theorem MvPowerSeries.eval₂_C (r : R) :
    MvPowerSeries.eval₂ φ a hpow hcof hφ (C σ R r) = φ r := by
  rw [← MvPolynomial.coe_C, eval₂_coe, MvPolynomial.eval₂_C]

theorem MvPowerSeries.eval₂_X (s : σ) :
    MvPowerSeries.eval₂ φ a hpow hcof hφ (X s) = a s := by
  rw [← MvPolynomial.coe_X, eval₂_coe, MvPolynomial.eval₂_X]

noncomputable def MvPowerSeries.aeval
    [Algebra R S] (hc: Continuous (algebraMap R S)):
    MvPowerSeries σ R →ₐ[R] S where
  toRingHom := MvPowerSeries.eval₂ (algebraMap R S) a hpow hcof hc
  commutes' := fun r ↦ by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [← MvPowerSeries.c_eq_algebraMap, eval₂_C]

end MvPowerSeries_aeval
