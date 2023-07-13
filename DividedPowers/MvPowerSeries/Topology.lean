import Mathbin.RingTheory.PowerSeries.Basic
import Oneshot.MvPowerSeries.Order
import Oneshot.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.Topology.UniformSpace.Basic
import Mathbin.Topology.UniformSpace.Pi
import Mathbin.Topology.UniformSpace.Separation
import Mathbin.Topology.Order.Basic
import Mathbin.Data.Set.Finite
import Oneshot.Antidiagonal

-- import topology.algebra.infinite_sum.basic
-- import topology.algebra.infinite_sum.basic
theorem Finset.prod_one_add {ι α : Type _} [CommRing α] {f : ι → α} (s : Finset ι) :
    (s.Prod fun i => 1 + f i) = s.powerset.Sum fun t => t.Prod f :=
  by
  simp_rw [add_comm]
  rw [Finset.prod_add]
  congr
  ext t
  convert mul_one _
  apply Finset.prod_eq_one
  intro i hi; rfl
#align finset.prod_one_add Finset.prod_one_add

theorem MvPowerSeries.coeff_eq_apply {σ α : Type _} [Semiring α] (f : MvPowerSeries σ α)
    (d : σ →₀ ℕ) : MvPowerSeries.coeff α d f = f d :=
  rfl
#align mv_power_series.coeff_eq_apply MvPowerSeries.coeff_eq_apply

namespace MvPowerSeries

open Function

variable (σ : Type _) (α : Type _)

section Topological

variable [TopologicalSpace α]

/-- The pointwise topology on mv_power_series -/
instance : TopologicalSpace (MvPowerSeries σ α) :=
  Pi.topologicalSpace

/-- Components are continuous -/
theorem continuous_component : ∀ d : σ →₀ ℕ, Continuous fun a : MvPowerSeries σ α => a d :=
  continuous_pi_iff.mp continuous_id
#align mv_power_series.continuous_component MvPowerSeries.continuous_component

variable {σ α}

/-- coeff are continuous-/
theorem continuous_coeff [Semiring α] (d : σ →₀ ℕ) : Continuous (MvPowerSeries.coeff α d) :=
  continuous_component σ α d
#align mv_power_series.continuous_coeff MvPowerSeries.continuous_coeff

/-- constant_coeff is continuous -/
theorem continuous_constantCoeff [Semiring α] : Continuous (constantCoeff σ α) :=
  continuous_component σ α 0
#align mv_power_series.continuous_constant_coeff MvPowerSeries.continuous_constantCoeff

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring α] {ι : Type _} (f : ι → MvPowerSeries σ α)
    (u : Filter ι) (g : MvPowerSeries σ α) :
    Filter.Tendsto f u (nhds g) ↔
      ∀ d : σ →₀ ℕ, Filter.Tendsto (fun i => coeff α d (f i)) u (nhds (coeff α d g)) :=
  by
  rw [nhds_pi]; rw [Filter.tendsto_pi]
  apply forall_congr'
  intro d
  rfl
#align mv_power_series.tendsto_iff_coeff_tendsto MvPowerSeries.tendsto_iff_coeff_tendsto

variable (σ α)

/-- The semiring topology on mv_power_series of a topological semiring -/
theorem topologicalSemiring [Semiring α] [TopologicalSemiring α] :
    TopologicalSemiring (MvPowerSeries σ α) :=
  { to_continuousAdd := by
      apply ContinuousAdd.mk
      apply continuous_pi
      intro d
      simp only [Pi.add_apply]
      change
        Continuous
          ((fun u : α × α => u.fst + u.snd) ∘ fun a : MvPowerSeries σ α × MvPowerSeries σ α =>
            (a.fst d, a.snd d))
      apply Continuous.comp
      exact continuous_add
      apply Continuous.prod_mk
      exact Continuous.fst' (continuous_component σ α d)
      exact Continuous.snd' (continuous_component σ α d)
    to_continuousMul := by
      apply ContinuousMul.mk
      apply continuous_pi
      intro d
      change
        Continuous fun a : MvPowerSeries σ α × MvPowerSeries σ α =>
          d.antidiagonal.sum fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => a.fst x.fst * a.snd x.snd
      apply continuous_finset_sum
      intro i hi
      change
        Continuous
          ((fun u : α × α => u.fst * u.snd) ∘ fun a : MvPowerSeries σ α × MvPowerSeries σ α =>
            (a.fst i.fst, a.snd i.snd))
      apply Continuous.comp
      exact continuous_mul
      apply Continuous.prod_mk
      exact Continuous.fst' (continuous_component σ α i.fst)
      exact Continuous.snd' (continuous_component σ α i.snd) }
#align mv_power_series.topological_semiring MvPowerSeries.topologicalSemiring

/-- The ring topology on mv_power_series of a topological ring -/
theorem topologicalRing [Ring α] [TopologicalRing α] : TopologicalRing (MvPowerSeries σ α) :=
  { to_topologicalSemiring := topologicalSemiring σ α
    to_continuousNeg := by
      apply ContinuousNeg.mk
      apply continuous_pi
      intro d
      change Continuous ((fun u : α => -u) ∘ fun a : MvPowerSeries σ α => a d)
      apply Continuous.comp
      exact continuous_neg
      exact continuous_component σ α d }
#align mv_power_series.topological_ring MvPowerSeries.topologicalRing

/-- mv_power_series on a t2_space form a t2_space -/
theorem t2Space [T2Space α] : T2Space (MvPowerSeries σ α) :=
  by
  apply T2Space.mk
  intro x y h
  rw [Function.ne_iff] at h 
  obtain ⟨d, h⟩ := h
  obtain ⟨u, v, huv⟩ := t2_separation h
  use (fun x => x d) ⁻¹' u
  use (fun x => x d) ⁻¹' v
  constructor
  exact IsOpen.preimage (continuous_component σ α d) huv.1
  constructor
  exact IsOpen.preimage (continuous_component σ α d) huv.2.1
  constructor
  simp only [Set.mem_preimage]; exact huv.2.2.1
  constructor
  simp only [Set.mem_preimage]; exact huv.2.2.2.1
  exact Disjoint.preimage _ huv.2.2.2.2
#align mv_power_series.t2_space MvPowerSeries.t2Space

end Topological

section Uniform

variable [UniformSpace α]

/-- The componentwise uniformity on mv_power_series -/
instance uniformSpace : UniformSpace (MvPowerSeries σ α) :=
  Pi.uniformSpace fun i : σ →₀ ℕ => α
#align mv_power_series.uniform_space MvPowerSeries.uniformSpace

/-- Components are uniformly continuous -/
theorem uniformContinuous_component :
    ∀ d : σ →₀ ℕ, UniformContinuous fun a : MvPowerSeries σ α => a d :=
  uniformContinuous_pi.mp uniformContinuous_id
#align mv_power_series.uniform_continuous_component MvPowerSeries.uniformContinuous_component

/-- The uniform_add_group structure on mv_power_series of a uniform_add_group -/
theorem uniformAddGroup [AddGroup α] [UniformAddGroup α] : UniformAddGroup (MvPowerSeries σ α) :=
  by
  apply UniformAddGroup.mk
  rw [uniformContinuous_pi]
  intro d
  let g : MvPowerSeries σ α × MvPowerSeries σ α → α :=
    (fun u : α × α => u.fst - u.snd) ∘ fun x => (x.fst d, x.snd d)
  change UniformContinuous g
  apply UniformContinuous.comp
  exact uniformContinuous_sub
  apply UniformContinuous.prod_mk
  change
    UniformContinuous
      ((fun x : MvPowerSeries σ α => x d) ∘ fun a : MvPowerSeries σ α × MvPowerSeries σ α => a.fst)
  apply UniformContinuous.comp
  apply uniform_continuous_component
  exact uniformContinuous_fst
  change
    UniformContinuous
      ((fun x : MvPowerSeries σ α => x d) ∘ fun a : MvPowerSeries σ α × MvPowerSeries σ α => a.snd)
  apply UniformContinuous.comp
  apply uniform_continuous_component
  exact uniformContinuous_snd
#align mv_power_series.uniform_add_group MvPowerSeries.uniformAddGroup

/-- Completeness of the uniform structure on mv_power_series -/
theorem completeSpace [AddGroup α] [CompleteSpace α] : CompleteSpace (MvPowerSeries σ α) :=
  by
  apply CompleteSpace.mk
  intro f hf
  suffices : ∀ d, ∃ x, (f.map fun a => a d) ≤ nhds x
  use fun d => (this d).some
  rw [nhds_pi, Filter.le_pi]
  intro d
  exact (this d).choose_spec
  intro d
  use lim (f.map fun a => a d)
  exact (Cauchy.map hf (uniform_continuous_component σ α d)).le_nhds_lim
#align mv_power_series.complete_space MvPowerSeries.completeSpace

/-- Separation of the uniform structure on mv_power_series -/
theorem separatedSpace [SeparatedSpace α] : SeparatedSpace (MvPowerSeries σ α) :=
  by
  rw [separated_iff_t2]
  have : _root_.t2_space α; rw [← separated_iff_t2]; infer_instance
  exact T2Space σ α
#align mv_power_series.separated_space MvPowerSeries.separatedSpace

/-  rw separated_def,
      intros x y hr,
      ext d,
      exact uniform_space.eq_of_separated_of_uniform_continuous
        (uniform_continuous_component σ α d) hr, -/
theorem uniform_topologicalRing [Ring α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (MvPowerSeries σ α) :=
  { to_continuousAdd := by
      haveI := UniformAddGroup σ α
      apply ContinuousAdd.mk
      apply UniformContinuous.continuous
      exact uniformContinuous_add
    to_continuousMul := by
      apply ContinuousMul.mk
      apply continuous_pi
      intro d
      change
        Continuous fun a : MvPowerSeries σ α × MvPowerSeries σ α =>
          d.antidiagonal.sum fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => a.fst x.fst * a.snd x.snd
      apply continuous_finset_sum
      intro i hi
      change
        Continuous
          ((fun u : α × α => u.fst * u.snd) ∘ fun a : MvPowerSeries σ α × MvPowerSeries σ α =>
            (a.fst i.fst, a.snd i.snd))
      apply Continuous.comp
      exact continuous_mul
      apply Continuous.prod_mk
      exact Continuous.fst' (continuous_component σ α i.fst)
      exact Continuous.snd' (continuous_component σ α i.snd)
    to_continuousNeg := by
      haveI := UniformAddGroup σ α
      apply ContinuousNeg.mk
      apply UniformContinuous.continuous
      exact uniformContinuous_neg }
#align mv_power_series.uniform_topological_ring MvPowerSeries.uniform_topologicalRing

end Uniform

example [σ_ne : Nonempty σ] : NoMaxOrder (σ →₀ ℕ) :=
  by
  apply NoMaxOrder.mk
  intro a
  use a + Finsupp.single σ_ne.some 1
  simp only [lt_iff_le_and_ne, zero_le, le_add_iff_nonneg_right, Ne.def, self_eq_add_right,
    Finsupp.single_eq_zero, Nat.one_ne_zero, not_false_iff, and_self_iff]

section

variable {σ α}

variable [TopologicalSpace α] [CommRing α] [TopologicalRing α]

theorem variables_tendsto_zero :
    Filter.Tendsto (fun s : σ => (X s : MvPowerSeries σ α)) Filter.cofinite (nhds 0) := by
  classical
  simp only [tendsto_pi_nhds, Pi.zero_apply]
  intro d
  intro s hs
  simp only [Filter.mem_map, Filter.mem_cofinite]
  rw [← Set.preimage_compl]
  by_cases h : ∃ i, d = Finsupp.single i 1
  obtain ⟨i, rfl⟩ := h
  apply Set.Finite.subset (Set.finite_singleton i)
  intro x
  rw [Set.mem_preimage]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [not_imp_comm]
  intro hx
  convert mem_of_mem_nhds hs
  rw [← coeff_eq_apply (X x) (Finsupp.single i 1)]
  rw [coeff_X]
  rw [if_neg]
  intro hx'
  rw [Finsupp.ext_iff] at hx' 
  apply zero_ne_one' ℕ
  specialize hx' x
  simpa only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hx)] using hx'
  convert Set.finite_empty
  rw [Set.eq_empty_iff_forall_not_mem]
  intro x
  simp only [Set.mem_preimage, Set.not_mem_compl_iff]
  convert mem_of_mem_nhds hs
  rw [← coeff_eq_apply (X x) d]
  rw [coeff_X]
  rw [if_neg]
  intro h'
  apply h
  exact ⟨x, h'⟩
#align mv_power_series.variables_tendsto_zero MvPowerSeries.variables_tendsto_zero

theorem tendsto_pow_of_constantCoeff_nilpotent {f : MvPowerSeries σ α}
    (hf : IsNilpotent (constantCoeff σ α f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  rw [MvPowerSeries.tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_zero]
  apply tendsto_atTop_of_eventually_const
  intro n hn
  exact coeff_eq_zero_of_constant_coeff_nilpotent f m hm d n hn
#align mv_power_series.tendsto_pow_of_constant_coeff_nilpotent MvPowerSeries.tendsto_pow_of_constantCoeff_nilpotent

theorem tendsto_pow_of_constantCoeff_zero {f : MvPowerSeries σ α} (hf : constantCoeff σ α f = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) :=
  by
  apply tendsto_pow_of_constant_coeff_nilpotent
  rw [hf]
  exact IsNilpotent.zero
#align mv_power_series.tendsto_pow_of_constant_coeff_zero MvPowerSeries.tendsto_pow_of_constantCoeff_zero

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [DiscreteTopology α] (f : MvPowerSeries σ α) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) ↔ IsNilpotent (constantCoeff σ α f) :=
  by
  constructor
  · intro h
    suffices : Filter.Tendsto (fun n : ℕ => constant_coeff σ α (f ^ n)) Filter.atTop (nhds 0)
    simp only [Filter.tendsto_def] at this 
    specialize this {0} _
    suffices : ∀ x : α, {x} ∈ nhds x; exact this 0
    rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
    simp only [map_pow, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage,
      Set.mem_singleton_iff] at this 
    obtain ⟨m, hm⟩ := this
    use m; apply hm m (le_refl m)
    rw [← Filter.tendsto_map'_iff]
    simp only [Filter.Tendsto, Filter.map_le_iff_le_comap] at h ⊢
    apply le_trans h
    apply Filter.comap_mono
    rw [← Filter.map_le_iff_le_comap]
    exact continuous_constant_coeff.continuous_at
  exact tendsto_of_pow_of_constant_coeff_nilpotent
#align mv_power_series.tendsto_pow_of_constant_coeff_nilpotent_iff MvPowerSeries.tendsto_pow_of_constantCoeff_nilpotent_iff

end

section Summable

variable [Semiring α] [TopologicalSpace α]

variable {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ α) :
    HasSum (fun d : σ →₀ ℕ => monomial α d (coeff α d f)) f :=
  by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d _
  · rw [← coeff_apply f d, ← coeff_apply (monomial α d (coeff α d f)) d, coeff_apply]
    rw [coeff_monomial_same]
  · intro b h
    change coeff α d ((monomial α b) ((coeff α b) f)) = 0
    rw [coeff_monomial_ne (Ne.symm h)]
#align mv_power_series.has_sum_of_monomials_self MvPowerSeries.hasSum_of_monomials_self

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space α] (f : MvPowerSeries σ α) :
    f = tsum fun d : σ →₀ ℕ => monomial α d (coeff α d f) := by
  classical
  haveI := MvPowerSeries.t2Space σ α
  simp only [tsum, dif_pos f.has_sum_of_monomials_self.summable]
  exact HasSum.unique f.has_sum_of_monomials_self (Classical.choose_spec _)
#align mv_power_series.as_tsum MvPowerSeries.as_tsum

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_homogeneous_components_self (w : σ → ℕ) (f : MvPowerSeries σ α) :
    HasSum (fun p => homogeneousComponent w p f) f :=
  by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single (weight w d) _
  · rw [← coeff_apply f d]
    rw [← coeff_apply (homogeneous_component w (weight w d) f) d]
    rw [coeff_homogeneous_component]
    simp only [eq_self_iff_true, if_true]
  · intro p h
    rw [← coeff_apply (homogeneous_component w p f) d]
    rw [coeff_homogeneous_component]
    rw [if_neg (Ne.symm h)]
#align mv_power_series.has_sum_of_homogeneous_components_self MvPowerSeries.hasSum_of_homogeneous_components_self

theorem homogeneous_components_self_summable (w : σ → ℕ) (f : MvPowerSeries σ α) :
    Summable fun p => homogeneousComponent w p f :=
  (hasSum_of_homogeneous_components_self w f).Summable
#align mv_power_series.homogeneous_components_self_summable MvPowerSeries.homogeneous_components_self_summable

theorem as_tsum_of_homogeneous_components_self [T2Space α] (w : σ → ℕ) (f : MvPowerSeries σ α) :
    f = tsum fun p => homogeneousComponent w p f := by
  classical
  haveI := T2Space σ α
  apply HasSum.unique (has_sum_of_homogeneous_components_self w f)
  simp only [tsum, dif_pos (homogeneous_components_self_summable w f)]
  apply Classical.choose_spec _
#align mv_power_series.as_tsum_of_homogeneous_components_self MvPowerSeries.as_tsum_of_homogeneous_components_self

end Summable

end MvPowerSeries

