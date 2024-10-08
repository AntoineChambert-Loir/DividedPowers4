import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.RingTheory.MvPowerSeries.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Order

-- In PR 14866 and 14989

/-! # Topology on power series

In this file we define the possible topologies on power series.


-/
theorem Finset.prod_one_add {ι α : Type _} [DecidableEq ι] [CommRing α] {f : ι → α} (s : Finset ι) :
    (s.prod fun i => 1 + f i) = s.powerset.sum fun t => t.prod f := by
  simp_rw [add_comm, Finset.prod_add]
  congr
  ext t
  convert mul_one (Finset.prod t fun a => f a)
  exact Finset.prod_eq_one (fun i _ => rfl)

theorem MvPowerSeries.coeff_eq_apply {σ α : Type _} [Semiring α] (f : MvPowerSeries σ α)
    (d : σ →₀ ℕ) : MvPowerSeries.coeff α d f = f d :=
  rfl

namespace MvPowerSeries

open Function

variable (σ : Type _) (α : Type _)

section Topological

variable [TopologicalSpace α]

namespace WithPiTopology

/-- The pointwise topology on MvPowerSeries -/
scoped instance topologicalSpace : TopologicalSpace (MvPowerSeries σ α) :=
  Pi.topologicalSpace

/-- Components are continuous -/
theorem continuous_component :
    ∀ d : σ →₀ ℕ, Continuous fun a : MvPowerSeries σ α => a d :=
  continuous_pi_iff.mp continuous_id

variable {σ α}

/-- coeff are continuous -/
theorem continuous_coeff [Semiring α] (d : σ →₀ ℕ) :
    Continuous (MvPowerSeries.coeff α d) :=
  continuous_component σ α d

/-- constant_coeff is continuous -/
theorem continuous_constantCoeff [Semiring α] :
    Continuous (constantCoeff σ α) :=
  continuous_component σ α 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring α] {ι : Type _}
    (f : ι → MvPowerSeries σ α) (u : Filter ι) (g : MvPowerSeries σ α) :
    Filter.Tendsto f u (nhds g) ↔
    ∀ d : σ →₀ ℕ, Filter.Tendsto (fun i => coeff α d (f i)) u (nhds (coeff α d g)) := by
  rw [nhds_pi, Filter.tendsto_pi]
  exact forall_congr' (fun d => Iff.rfl)

variable (σ α)

/-- The semiring topology on MvPowerSeries of a topological semiring -/
scoped instance topologicalSemiring [Semiring α] [TopologicalSemiring α] :
    TopologicalSemiring (MvPowerSeries σ α) where
    continuous_add := continuous_pi fun d => Continuous.comp continuous_add
      (Continuous.prod_mk (Continuous.fst' (continuous_component σ α d))
        (Continuous.snd' (continuous_component σ α d)))
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ (fun i _ => Continuous.comp
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ α i.fst))
        (Continuous.snd' (continuous_component σ α i.snd))))

/-- The ring topology on MvPowerSeries of a topological ring -/
scoped instance topologicalRing [Ring α] [TopologicalRing α] :
    TopologicalRing (MvPowerSeries σ α) :=
  { topologicalSemiring σ α with
    continuous_neg := continuous_pi fun d ↦ Continuous.comp continuous_neg
      (continuous_component σ α d) }

/-- MvPowerSeries on a T2Space form a T2Space -/
scoped instance t2Space [T2Space α] : T2Space (MvPowerSeries σ α) where
  t2 x y h := by
    obtain ⟨d, h⟩ := Function.ne_iff.mp h
    obtain ⟨u, v, ⟨hu, hv, hx, hy, huv⟩⟩ := t2_separation h
    exact ⟨(fun x => x d) ⁻¹' u, (fun x => x d) ⁻¹' v,
      IsOpen.preimage (continuous_component σ α d) hu,
      IsOpen.preimage (continuous_component σ α d) hv, hx, hy,
      Disjoint.preimage _ huv⟩

end WithPiTopology

end Topological

section Uniform

namespace WithPiUniformity

open WithPiTopology

variable [UniformSpace α]

/-- The componentwise uniformity on MvPowerSeries -/
scoped instance uniformSpace : UniformSpace (MvPowerSeries σ α) :=
  Pi.uniformSpace fun _ : σ →₀ ℕ => α

/-- Components are uniformly continuous -/
theorem uniformContinuous_component :
    ∀ d : σ →₀ ℕ, UniformContinuous fun a : MvPowerSeries σ α => a d :=
  uniformContinuous_pi.mp uniformContinuous_id

/-- The uniform_add_group structure on MvPowerSeries of a uniform_add_group -/
scoped instance uniformAddGroup [AddGroup α] [UniformAddGroup α] :
    UniformAddGroup (MvPowerSeries σ α) where
  uniformContinuous_sub := uniformContinuous_pi.mpr fun _ => UniformContinuous.comp
    uniformContinuous_sub
    (UniformContinuous.prod_mk
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_fst)
      (UniformContinuous.comp (uniformContinuous_component _ _ _) uniformContinuous_snd))

/-- Completeness of the uniform structure on MvPowerSeries -/
scoped instance completeSpace [AddGroup α] [CompleteSpace α] :
    CompleteSpace (MvPowerSeries σ α) where
  complete := by
    intro f hf
    suffices ∀ d, ∃ x, (f.map fun a => a d) ≤ nhds x by
      use fun d => (this d).choose
      rw [nhds_pi, Filter.le_pi]
      exact fun d => (this d).choose_spec
    intro d
    use lim (f.map fun a => a d)
    exact (Cauchy.map hf (uniformContinuous_component σ α d)).le_nhds_lim

/-- Separation of the uniform structure on MvPowerSeries -/
scoped instance t0Space [T0Space α] : T0Space (MvPowerSeries σ α) := by
  suffices T2Space (MvPowerSeries σ α) by infer_instance
  exact WithPiTopology.t2Space σ α

scoped instance uniform_topologicalRing [Ring α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (MvPowerSeries σ α) :=
  { uniformAddGroup σ α with
    continuous_add :=  (@uniformContinuous_add _ _ _ (uniformAddGroup σ α)).continuous
    continuous_mul := continuous_pi fun _ => continuous_finset_sum _ fun i _ => Continuous.comp
      continuous_mul (Continuous.prod_mk (Continuous.fst' (continuous_component σ α i.fst))
        (Continuous.snd' (continuous_component σ α i.snd)))
    continuous_neg := (@uniformContinuous_neg _ _ _ (uniformAddGroup σ α)).continuous
    }

end WithPiUniformity

end Uniform

example [σ_ne : Nonempty σ] : NoMaxOrder (σ →₀ ℕ) where
  exists_gt := fun a => by
    use a + Finsupp.single σ_ne.some 1
    simp only [lt_iff_le_and_ne, zero_le, le_add_iff_nonneg_right, ne_eq, self_eq_add_right,
      Finsupp.single_eq_zero, Nat.one_ne_zero, not_false_iff, and_self_iff]

section

variable {σ α} [DecidableEq σ]

variable [TopologicalSpace α] [CommRing α] [TopologicalRing α]

open WithPiTopology WithPiUniformity

theorem continuous_C :
    Continuous (C σ α) := by
  apply continuous_of_continuousAt_zero
  rw [continuousAt_pi]
  intro d
  change ContinuousAt (fun y => coeff α d ((C σ α) y)) 0
  by_cases hd : d = 0
  · convert continuousAt_id
    rw [hd, coeff_zero_C, id_eq]
  · convert continuousAt_const
    rw [coeff_C, if_neg hd]

omit [TopologicalRing α] in
theorem variables_tendsto_zero :
    Filter.Tendsto (fun s : σ => (X s : MvPowerSeries σ α)) Filter.cofinite (nhds 0) := by
  classical
  rw [tendsto_pi_nhds]
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
    rw [← coeff_eq_apply (X x) (Finsupp.single i 1), coeff_X, if_neg]
    rfl
    · simp only [Finsupp.single_eq_single_iff, Ne.symm hx, and_true, one_ne_zero, and_self,
      or_self, not_false_eq_true]
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

omit [DecidableEq σ] [TopologicalRing α] in
theorem tendsto_pow_zero_of_constantCoeff_nilpotent {f : MvPowerSeries σ α}
    (hf : IsNilpotent (constantCoeff σ α f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  classical
  obtain ⟨m, hm⟩ := hf
  simp_rw [tendsto_iff_coeff_tendsto, coeff_zero]
  exact fun d =>  tendsto_atTop_of_eventually_const fun n hn =>
    coeff_eq_zero_of_constantCoeff_nilpotent hm hn

omit [DecidableEq σ] [TopologicalRing α] in
theorem tendsto_pow_zero_of_constantCoeff_zero {f : MvPowerSeries σ α} (hf : constantCoeff σ α f = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) := by
  apply tendsto_pow_zero_of_constantCoeff_nilpotent
  rw [hf]
  exact IsNilpotent.zero

omit [DecidableEq σ] [TopologicalRing α] in
/-- Bourbaki, Algèbre, chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [DiscreteTopology α] (f : MvPowerSeries σ α) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) ↔
      IsNilpotent (constantCoeff σ α f) := by
  refine' ⟨_, tendsto_pow_zero_of_constantCoeff_nilpotent ⟩
  · intro h
    suffices Filter.Tendsto (fun n : ℕ => constantCoeff σ α (f ^ n)) Filter.atTop (nhds 0) by
      simp only [Filter.tendsto_def] at this
      specialize this {0} _
      suffices  ∀ x : α, {x} ∈ nhds x by exact this 0
      rw [← discreteTopology_iff_singleton_mem_nhds]; infer_instance
      simp only [map_pow, Filter.mem_atTop_sets, ge_iff_le, Set.mem_preimage,
        Set.mem_singleton_iff] at this
      obtain ⟨m, hm⟩ := this
      use m
      apply hm m (le_refl m)
    simp only [← @comp_apply _ α ℕ]
    rw [← Filter.tendsto_map'_iff]
    simp only [Filter.Tendsto, Filter.map_le_iff_le_comap] at h ⊢
    apply le_trans h
    apply Filter.comap_mono
    rw [← Filter.map_le_iff_le_comap]
    apply continuous_constantCoeff.continuousAt

end

section Summable

variable [Semiring α] [TopologicalSpace α]

open WithPiTopology

variable {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : MvPowerSeries σ α) :
    HasSum (fun d : σ →₀ ℕ => monomial α d (coeff α d f)) f := by
  rw [Pi.hasSum]
  intro d
  convert hasSum_single d ?_ using 1
  exact (coeff_monomial_same d _).symm
  exact fun d' h ↦ coeff_monomial_ne (Ne.symm h) _

/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space α] (f : MvPowerSeries σ α) :
    f = tsum fun d : σ →₀ ℕ => monomial α d (coeff α d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

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

theorem homogeneous_components_self_summable (w : σ → ℕ) (f : MvPowerSeries σ α) :
    Summable fun p => homogeneousComponent w p f :=
  (hasSum_of_homogeneous_components_self w f).summable

theorem as_tsum_of_homogeneous_components_self [T2Space α] (w : σ → ℕ) (f : MvPowerSeries σ α) :
    f = tsum fun p => homogeneousComponent w p f := by
  haveI := t2Space σ α
  exact HasSum.unique (hasSum_of_homogeneous_components_self w f)
   (homogeneous_components_self_summable w f).hasSum

end Summable

end MvPowerSeries
