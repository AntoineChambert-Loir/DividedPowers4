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

theorem Continuous.tendsto_apply_pow_of_constant_coeff_zero (φ : MvPowerSeries σ α →ₐ[α] R)
    (hφ : Continuous φ) (s : σ) : Filter.Tendsto (fun n : ℕ => φ (X s ^ n)) Filter.atTop (nhds 0) :=
  by
  rw [← φ.map_zero]
  refine' Filter.Tendsto.comp hφ.continuousAt (tendsto_pow_of_constantCoeff_zero _)
  rw [constantCoeff_X]
#align continuous.tendsto_apply_pow_of_constant_coeff_zero
  Continuous.tendsto_apply_pow_of_constant_coeff_zero

theorem Continuous.apply_variables (φ : MvPowerSeries σ α →ₐ[α] R) (hφ : Continuous φ) :
    Filter.Tendsto (fun s : σ => φ (X s)) Filter.cofinite (nhds 0) := by
  rw [← φ.map_zero]
  exact Filter.Tendsto.comp hφ.continuousAt variables_tendsto_zero
#align continuous.apply_variables Continuous.apply_variables

