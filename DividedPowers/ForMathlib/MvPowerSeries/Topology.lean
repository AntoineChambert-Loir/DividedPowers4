import Mathlib.RingTheory.PowerSeries.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Order
import DividedPowers.ForMathlib.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Finite
import DividedPowers.ForMathlib.Antidiagonal

theorem Finset.prod_one_add {ι α : Type _} [CommRing α] {f : ι → α} (s : Finset ι) :
    (s.prod fun i => 1 + f i) = s.powerset.sum fun t => t.prod f := by
  simp_rw [add_comm, Finset.prod_add]
  congr
  ext t
  convert mul_one (Finset.prod t fun a => f a)
  exact Finset.prod_eq_one (fun i _ => rfl)
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
    (u : Filter ι) (g : MvPowerSeries σ α) : Filter.Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Filter.Tendsto (fun i => coeff α d (f i)) u (nhds (coeff α d g)) := by
  rw [nhds_pi, Filter.tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)
#align mv_power_series.tendsto_iff_coeff_tendsto MvPowerSeries.tendsto_iff_coeff_tendsto

variable (σ α)

/-- The semiring topology on mv_power_series of a topological semiring -/
theorem topologicalSemiring [Semiring α] [TopologicalSemiring α] :
    TopologicalSemiring (MvPowerSeries σ α) where
    continuous_add := continuous_pi fun d => Continuous.comp continuous_add 
      (Continuous.prod_mk (Continuous.fst' (continuous_component σ α d))
        (Continuous.snd' (continuous_component σ α d)))
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ (fun i _ => Continuous.comp 
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ α i.fst))
        (Continuous.snd' (continuous_component σ α i.snd))))
#align mv_power_series.topological_semiring MvPowerSeries.topologicalSemiring
 
/-- The ring topology on mv_power_series of a topological ring -/
theorem topologicalRing [Ring α] [TopologicalRing α] : TopologicalRing (MvPowerSeries σ α) :=
  { topologicalSemiring σ α with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg 
      (continuous_component σ α d) }
#align mv_power_series.topological_ring MvPowerSeries.topologicalRing

/-- mv_power_series on a t2_space form a t2_space -/
theorem t2Space [T2Space α] : T2Space (MvPowerSeries σ α) := by
  apply T2Space.mk
  intro x y h
  rw [Function.ne_iff] at h 
  obtain ⟨d, h⟩ := h
  obtain ⟨u, v, huv⟩ := t2_separation h
  use (fun x => x d) ⁻¹' u, (fun x => x d) ⁻¹' v, 
    IsOpen.preimage (continuous_component σ α d) huv.1,
    IsOpen.preimage (continuous_component σ α d) huv.2.1, huv.2.2.1, huv.2.2.2.1
  exact Disjoint.preimage _ huv.2.2.2.2
#align mv_power_series.t2_space MvPowerSeries.t2Space

end Topological

section Uniform

variable [UniformSpace α]

/-- The componentwise uniformity on mv_power_series -/
instance uniformSpace : UniformSpace (MvPowerSeries σ α) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => α
#align mv_power_series.uniform_space MvPowerSeries.uniformSpace

/-- Components are uniformly continuous -/
theorem uniformContinuous_component :
    ∀ d : σ →₀ ℕ, UniformContinuous fun a : MvPowerSeries σ α => a d :=
  uniformContinuous_pi.mp uniformContinuous_id
#align mv_power_series.uniform_continuous_component MvPowerSeries.uniformContinuous_component

/-- The uniform_add_group structure on mv_power_series of a uniform_add_group -/
theorem uniformAddGroup [AddGroup α] [UniformAddGroup α] : UniformAddGroup (MvPowerSeries σ α) where 
  uniformContinuous_sub := uniformContinuous_pi.mpr fun _ => UniformContinuous.comp 
    uniformContinuous_sub
    (UniformContinuous.prod_mk 
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_fst) 
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_snd))
#align mv_power_series.uniform_add_group MvPowerSeries.uniformAddGroup

/-- Completeness of the uniform structure on mv_power_series -/
theorem completeSpace [AddGroup α] [CompleteSpace α] : CompleteSpace (MvPowerSeries σ α) where
  complete := by
    intro f hf
    suffices : ∀ d, ∃ x, (f.map fun a => a d) ≤ nhds x
    . use fun d => (this d).choose
      rw [nhds_pi, Filter.le_pi]
      exact fun d => (this d).choose_spec
    intro d
    use lim (f.map fun a => a d)
    exact (Cauchy.map hf (uniformContinuous_component σ α d)).le_nhds_lim
#align mv_power_series.complete_space MvPowerSeries.completeSpace

/-- Separation of the uniform structure on mv_power_series -/
theorem separatedSpace [SeparatedSpace α] : SeparatedSpace (MvPowerSeries σ α) := by
  rw [separated_iff_t2]
  have : _root_.T2Space α := by
    rw [← separated_iff_t2]; infer_instance
  exact t2Space σ α
#align mv_power_series.separated_space MvPowerSeries.separatedSpace

theorem uniform_topologicalRing [Ring α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (MvPowerSeries σ α) :=
  { uniformAddGroup σ α with 
    continuous_add :=  uniformContinuous_add.continuous
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ fun i _ => Continuous.comp 
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ α i.fst))
        (Continuous.snd' (continuous_component σ α i.snd)))
    continuous_neg := uniformContinuous_neg.continuous }
#align mv_power_series.uniform_topological_ring MvPowerSeries.uniform_topologicalRing

end Uniform

example [σ_ne : Nonempty σ] : NoMaxOrder (σ →₀ ℕ) where
  exists_gt := fun a => by
    use a + Finsupp.single σ_ne.some 1
    simp only [lt_iff_le_and_ne, zero_le, le_add_iff_nonneg_right, Ne.def, self_eq_add_right,
      Finsupp.single_eq_zero, Nat.one_ne_zero, not_false_iff, and_self_iff]

section

variable {σ α}

variable [TopologicalSpace α] [CommRing α] [TopologicalRing α]

theorem variables_tendsto_zero :
    Filter.Tendsto (fun s : σ => (X s : MvPowerSeries σ α)) Filter.cofinite (nhds 0) := by
  classical
  rw [tendsto_pi_nhds]
  simp_rw [Pi.zero_apply]
  intro d s hs
  rw [Filter.mem_map, Filter.mem_cofinite, ← Set.preimage_compl]
  by_cases h : ∃ i, d = Finsupp.single i 1
  . obtain ⟨i, rfl⟩ := h
    apply Set.Finite.subset (Set.finite_singleton i)
    intro x
    simp only [OfNat.ofNat, Zero.zero] at hs 
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, not_imp_comm]
    intro hx
    convert mem_of_mem_nhds hs
    rw [← coeff_eq_apply (X x) (Finsupp.single i 1), coeff_X,
      if_neg (by simp only [Finsupp.single_eq_single_iff, and_true, or_false, Ne.symm hx])]
    rfl      
  . convert Set.finite_empty
    rw [Set.eq_empty_iff_forall_not_mem]
    intro x
    rw [Set.mem_preimage, Set.not_mem_compl_iff]
    convert mem_of_mem_nhds hs using 1
    rw [← coeff_eq_apply (X x) d, coeff_X, if_neg]
    rfl
    . intro h'
      apply h
      exact ⟨x, h'⟩
#align mv_power_series.variables_tendsto_zero MvPowerSeries.variables_tendsto_zero

theorem tendsto_pow_of_constantCoeff_nilpotent {f : MvPowerSeries σ α}
    (hf : IsNilpotent (constantCoeff σ α f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [MvPowerSeries.tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d =>  tendsto_atTop_of_eventually_const fun n hn => 
    coeff_eq_zero_of_constantCoeff_nilpotent f m hm d n hn
#align mv_power_series.tendsto_pow_of_constant_coeff_nilpotent MvPowerSeries.tendsto_pow_of_constantCoeff_nilpotent

theorem tendsto_pow_of_constantCoeff_zero {f : MvPowerSeries σ α} (hf : constantCoeff σ α f = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  apply tendsto_pow_of_constantCoeff_nilpotent
  rw [hf]
  exact IsNilpotent.zero
#align mv_power_series.tendsto_pow_of_constant_coeff_zero MvPowerSeries.tendsto_pow_of_constantCoeff_zero

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [DiscreteTopology α] (f : MvPowerSeries σ α) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) ↔ 
      IsNilpotent (constantCoeff σ α f) := by
  refine' ⟨_, tendsto_pow_of_constantCoeff_nilpotent ⟩
  · intro h
    suffices : Filter.Tendsto (fun n : ℕ => constantCoeff σ α (f ^ n)) Filter.atTop (nhds 0)
    simp only [Filter.tendsto_def] at this 
    specialize this {0} _
    suffices : ∀ x : α, {x} ∈ nhds x; exact this 0
    rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
    simp only [map_pow, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage,
      Set.mem_singleton_iff] at this 
    obtain ⟨m, hm⟩ := this
    use m
    apply hm m (le_refl m) 
    change Filter.Tendsto (constantCoeff σ α ∘ fun n => f ^ n) Filter.atTop (nhds 0)
    rw [← Filter.tendsto_map'_iff]
    simp only [Filter.Tendsto, Filter.map_le_iff_le_comap] at h ⊢
    apply le_trans h
    apply Filter.comap_mono
    rw [← Filter.map_le_iff_le_comap]
    apply continuous_constantCoeff.continuousAt
#align mv_power_series.tendsto_pow_of_constant_coeff_nilpotent_iff
  MvPowerSeries.tendsto_pow_of_constantCoeff_nilpotent_iff

end

section Summable

variable [Semiring α] [TopologicalSpace α]

variable {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ α) :
    HasSum (fun d : σ →₀ ℕ => monomial α d (coeff α d f)) f := by
  rw [Pi.hasSum]
  intro d
  have hd : ∀ (d' : σ →₀ ℕ), d' ≠ d → (monomial α d') ((coeff α d') f) d = 0 := by
    intro d' h
    change coeff α d ((monomial α d') ((coeff α d') f)) = 0
    rw [coeff_monomial_ne (Ne.symm h)]
  convert hasSum_single d hd using 1
  · rw [← coeff_apply f d, ← coeff_apply (monomial α d (coeff α d f)) d, coeff_apply,
      coeff_monomial_same]
#align mv_power_series.has_sum_of_monomials_self MvPowerSeries.hasSum_of_monomials_self

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space α] (f : MvPowerSeries σ α) :
    f = tsum fun d : σ →₀ ℕ => monomial α d (coeff α d f) := by
  haveI := MvPowerSeries.t2Space σ α
  apply HasSum.unique f.hasSum_of_monomials_self
  rw [tsum_def]
  rw [dif_pos f.hasSum_of_monomials_self.summable]
  split_ifs with h'
  . rw [← tsum_eq_finsum h']
    exact (f.hasSum_of_monomials_self.summable).hasSum
  . exact (Classical.choose_spec _)
#align mv_power_series.as_tsum MvPowerSeries.as_tsum

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_homogeneous_components_self (w : σ → ℕ) (f : MvPowerSeries σ α) :
    HasSum (fun p => homogeneousComponent w p f) f := by
  rw [Pi.hasSum]
  intro d
  have hd : ∀ (b' : ℕ), b' ≠ (weight w) d → (homogeneousComponent w b') f d = 0 := by
    intro p h
    rw [← coeff_apply (homogeneousComponent w p f) d, coeff_homogeneousComponent,
      if_neg (Ne.symm h)] 
  convert hasSum_single (weight w d) hd using 1
  · rw [← coeff_apply f d, ← coeff_apply (homogeneousComponent w (weight w d) f) d,
      coeff_homogeneousComponent]
    simp only [eq_self_iff_true, if_true]
#align mv_power_series.has_sum_of_homogeneous_components_self MvPowerSeries.hasSum_of_homogeneous_components_self

theorem homogeneous_components_self_summable (w : σ → ℕ) (f : MvPowerSeries σ α) :
    Summable fun p => homogeneousComponent w p f :=
  (hasSum_of_homogeneous_components_self w f).summable
#align mv_power_series.homogeneous_components_self_summable MvPowerSeries.homogeneous_components_self_summable

theorem as_tsum_of_homogeneous_components_self [T2Space α] (w : σ → ℕ) (f : MvPowerSeries σ α) :
    f = tsum fun p => homogeneousComponent w p f := by
  haveI := t2Space σ α
  exact HasSum.unique (hasSum_of_homogeneous_components_self w f)
   (homogeneous_components_self_summable w f).hasSum
#align mv_power_series.as_tsum_of_homogeneous_components_self MvPowerSeries.as_tsum_of_homogeneous_components_self

end Summable

end MvPowerSeries

