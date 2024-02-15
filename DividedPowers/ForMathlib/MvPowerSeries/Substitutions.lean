import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology

/- # Substitutions in power series

We follow Bourbaki, Algèbre, chap. 4, §4, n° 3 -/
/- # Substitutions in power series

We follow Bourbaki, Algèbre, chap. 4, §4, n° 3 -/
variable (α : Type _) [CommRing α]

variable (R : Type _) [CommRing R] [Algebra α R]

-- variables {ι : Type*} [nonempty ι] {J : ι → ideal R} (hJ : ideals_basis J)
-- instance zz1 : topological_space R := ideals_basis.topology hJ
-- instance zz2 := ideals_basis.to_topological_ring hJ
variable [TopologicalSpace R] [TopologicalRing R]

variable [TopologicalSpace α] [TopologicalRing α]

variable (σ : Type _)

open MvPowerSeries

-- set_option trace.class_instances true
example {α β γ : Type _} (φ : α → β) (ψ : β → γ) (f : Filter α) (g : Filter β) (h : Filter γ)
    (hφ : Filter.Tendsto φ f g) (hψ : Filter.Tendsto ψ g h) : Filter.Tendsto (ψ ∘ φ) f h := by
  refine' Filter.Tendsto.comp hψ hφ

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (a) -/
theorem Continuous.tendsto_apply_pow_zero_of_constantCoeff_zero {φ : MvPowerSeries σ α →ₐ[α] R}
    (hφ : Continuous φ) (s : σ) :
    Filter.Tendsto (fun n : ℕ => φ (X s ^ n)) Filter.atTop (nhds 0) := by
  rw [← φ.map_zero]
  refine' Filter.Tendsto.comp hφ.continuousAt (tendsto_pow_zero_of_constantCoeff_zero _)
  rw [constantCoeff_X]

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (b) -/
theorem Continuous.tendsto_apply_variables_zero_of_cofinite {φ : MvPowerSeries σ α →ₐ[α] R}
    (hφ : Continuous φ) :
    Filter.Tendsto (fun s : σ => φ (X s)) Filter.cofinite (nhds 0) := by
  rw [← φ.map_zero]
  exact Filter.Tendsto.comp hφ.continuousAt variables_tendsto_zero

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (i) (c) -/
theorem foo {Y : σ → R}
    (hY_pow : ∀ s : σ, Filter.Tendsto (fun n : ℕ => (Y s ^ n)) Filter.atTop (nhds 0))
    (hY_cof : ∀ s : σ, Filter.Tendsto (fun s : σ => (Y s)) Filter.cofinite (nhds 0)) :
    ∃ (φ : MvPowerSeries σ α →ₐ[α] R) (hφ : Continuous φ), ∀ (s : σ), φ (X s) = Y s := by
  sorry
