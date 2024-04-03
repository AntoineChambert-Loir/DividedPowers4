import DividedPowers.ForMathlib.MvPowerSeries.Topology

/-! # Topology on power series

In this file we define the possible topologies on power series.


-/

namespace PowerSeries

open Function

variable (α : Type _)

section Topological

variable [TopologicalSpace α]

namespace WithPiTopology

/-- The pointwise topology on PowerSeries -/
scoped instance topologicalSpace : TopologicalSpace (PowerSeries α) :=
  Pi.topologicalSpace

/-- Components are continuous -/
theorem continuous_component :
    ∀ d : Unit →₀ ℕ, Continuous fun a : PowerSeries α => a d :=
  continuous_pi_iff.mp continuous_id

variable {σ α}

/-- coeff are continuous -/
theorem continuous_coeff [Semiring α] (d : ℕ) :
    Continuous (PowerSeries.coeff α d) := continuous_component _ _

/-- constant_coeff is continuous -/
theorem continuous_constantCoeff [Semiring α] :
    Continuous (constantCoeff α) := continuous_component α 0

/-- A family of power series converges iff it converges coefficientwise -/
theorem tendsto_iff_coeff_tendsto [Semiring α] {ι : Type _}
    (f : ι → PowerSeries α) (u : Filter ι) (g : PowerSeries α) :
    Filter.Tendsto f u (nhds g) ↔
    ∀ d : ℕ, Filter.Tendsto (fun i => coeff α d (f i)) u (nhds (coeff α d g)) := by
  rw [nhds_pi, Filter.tendsto_pi]
  sorry
  --exact forall_congr' (fun d => Iff.rfl)

variable (σ α)

/-- The semiring topology on PowerSeries of a topological semiring -/
scoped instance topologicalSemiring [Semiring α] [TopologicalSemiring α] :
    TopologicalSemiring (PowerSeries α) := MvPowerSeries.WithPiTopology.topologicalSemiring Unit α


/-- The ring topology on PowerSeries of a topological ring -/
scoped instance topologicalRing [Ring α] [TopologicalRing α] :
    TopologicalRing (PowerSeries α) := MvPowerSeries.WithPiTopology.topologicalRing Unit α

/-- PowerSeries on a T2Space form a T2Space -/
scoped instance t2Space [T2Space α] : T2Space (PowerSeries α) :=
  MvPowerSeries.WithPiTopology.t2Space Unit α

end WithPiTopology

end Topological

section Uniform

namespace WithPiUniformity

open WithPiTopology

variable [UniformSpace α]

/-- The componentwise uniformity on PowerSeries -/
scoped instance uniformSpace : UniformSpace (PowerSeries α) :=
  MvPowerSeries.WithPiUniformity.uniformSpace Unit α

/-- Components are uniformly continuous -/
theorem uniformContinuous_component :
    ∀ d : Unit →₀ ℕ, UniformContinuous fun a : PowerSeries α => a d :=
  uniformContinuous_pi.mp uniformContinuous_id

/-- The uniform_add_group structure on PowerSeries of a uniform_add_group -/
scoped instance uniformAddGroup [AddGroup α] [UniformAddGroup α] :
    UniformAddGroup (PowerSeries α) :=
  MvPowerSeries.WithPiUniformity.uniformAddGroup Unit α

/-- Completeness of the uniform structure on PowerSeries -/
scoped instance completeSpace [AddGroup α] [CompleteSpace α] :
    CompleteSpace (PowerSeries α) :=
  MvPowerSeries.WithPiUniformity.completeSpace Unit α

/-- Separation of the uniform structure on PowerSeries -/
scoped instance t0Space [T0Space α] : T0Space (PowerSeries α) :=
  MvPowerSeries.WithPiUniformity.t0Space Unit α

scoped instance uniform_topologicalRing [Ring α] [UniformAddGroup α] [TopologicalRing α] :
    TopologicalRing (PowerSeries α) :=
  MvPowerSeries.WithPiUniformity.uniform_topologicalRing Unit α

end WithPiUniformity

end Uniform


section

variable {α}

variable [TopologicalSpace α] [CommRing α] [TopologicalRing α]

open WithPiTopology WithPiUniformity

theorem continuous_C : Continuous (C α) := MvPowerSeries.continuous_C

theorem tendsto_pow_zero_of_constantCoeff_nilpotent {f : PowerSeries α}
    (hf : IsNilpotent (constantCoeff α f)) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) :=
  MvPowerSeries.tendsto_pow_zero_of_constantCoeff_nilpotent hf

theorem tendsto_pow_zero_of_constantCoeff_zero {f : PowerSeries α} (hf : constantCoeff α f = 0) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) :=
  MvPowerSeries.tendsto_pow_zero_of_constantCoeff_zero hf

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, corollaire de la prop. 3 -/
theorem tendsto_pow_of_constantCoeff_nilpotent_iff [DiscreteTopology α] (f : PowerSeries α) :
    Filter.Tendsto (fun n : ℕ => f ^ n) Filter.atTop (nhds 0) ↔
      IsNilpotent (constantCoeff α f) :=
  MvPowerSeries.tendsto_pow_of_constantCoeff_nilpotent_iff f


end

section Summable

variable [Semiring α] [TopologicalSpace α]

open WithPiTopology MvPowerSeries.WithPiTopology

variable {σ α}

/-- A power series is the sum (in the sense of summable families) of its monomials -/
theorem hasSum_of_monomials_self (f : PowerSeries α) :
    HasSum (fun d : ℕ => monomial α d (coeff α d f)) f := by
  rw [Pi.hasSum]
  intro ud
  set d := ud ()
  have hd : ∀ (d' : ℕ), d' ≠ d → (coeff _ d ((monomial α d') ((coeff α d') f))) = 0 := by
    intro d' h
    rw [coeff_monomial, if_neg h.symm]
  convert hasSum_single d hd using 1
  · sorry/- rw [← MvPowerSeries.coeff_apply f ud, ← coeff_apply (monomial α d (coeff α d f)) d, coeff_apply,
      coeff_monomial_same] -/
  sorry

-- NOTE : this is duplicated
noncomputable def _root_.finsuppUnitEquiv (α : Type*) [Zero α] : (Unit →₀ α) ≃ α where
  toFun f := f ()
  invFun a := Finsupp.single () a
  left_inv := fun f ↦ by ext; simp
  right_inv := fun a ↦ by simp

--TODO: change the proof
/-- If the coefficient space is T2, then the power series is `tsum` of its monomials -/
theorem as_tsum [T2Space α] (f : PowerSeries α) :
    f = tsum fun d : ℕ => monomial α d (coeff α d f) :=
  (HasSum.tsum_eq (hasSum_of_monomials_self _)).symm

end Summable

end PowerSeries
