import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology

--import Mathlib.Topology.UniformSpace.CompleteSeparated

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



/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - Existence -/
theorem foo {Y : σ → R}
    (hY_pow : ∀ s : σ, Filter.Tendsto (fun n : ℕ => (Y s ^ n)) Filter.atTop (nhds 0))
    (hY_cof : ∀ s : σ, Filter.Tendsto (fun s : σ => (Y s)) Filter.cofinite (nhds 0))
    [τ : UniformSpace R] (ι : Type*) [Nonempty ι] [IsLinearTopology R ι] [CompleteSpace R]
    [T2Space R] :
    ∃ (φ : MvPowerSeries σ α →ₐ[α] R) (hφ : Continuous φ), ∀ (s : σ), φ (X s) = Y s := by
  set ψ : MvPolynomial σ α →ₐ[α] R :=
  { toFun     := fun f => MvPolynomial.aeval Y f
    map_one'  := by simp only [map_one]
    map_mul'  := by simp only [map_mul, forall_const]
    map_zero' := by simp only [map_zero]
    map_add'  := by simp only [map_add, forall_const]
    commutes' := by simp only [AlgHom.commutes, forall_const] } with hψ_def
  -- I should move this and di outside the proof
  letI : TopologicalSpace (MvPolynomial σ α) := TopologicalSpace.induced
    MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α)
  haveI di : DenseInducing (@MvPolynomial.toMvPowerSeries σ α _) := {
    induced := rfl
    dense   := by
      rw [DenseRange, Dense]
      intro f
      rw [mem_closure_iff]
      intro S hSopen hSf
      sorry }
  have hψ : Continuous ψ := by
    rw [continuous_def]
    intros U hU
    sorry
  let φ : MvPowerSeries σ α →ₐ[α] R :=
  { toFun     := DenseInducing.extend di ψ
    map_one'  := by rw [← MvPolynomial.coe_one, DenseInducing.extend_eq di hψ, map_one]
    map_mul'  := by
      simp only [AlgHom.mk_coe]
      sorry
    map_zero' := by
      rw [← MvPolynomial.coe_zero]
      simp only [AlgHom.mk_coe]
      erw [DenseInducing.extend_eq di hψ, map_zero]
    map_add'  := sorry
    commutes' := sorry }
  have : φ = DenseInducing.extend di ψ := rfl
  have hφ : Continuous φ := by
    rw [this]
    apply DenseInducing.continuous_extend di
    intro f
    use (φ f)
    rw [tendsto_nhds]
    intros U hUopen hUf
    rw [Filter.mem_comap]
    use (φ ⁻¹' U)
    constructor
    · rw [mem_nhds_iff]
      have := MvPolynomial.toMvPowerSeries ⁻¹' (⇑φ ⁻¹' U)
      sorry
    · intro P hP
      change DenseInducing.extend di ⇑(ψ) ↑P ∈ U at hP
      rw [DenseInducing.extend_eq di hψ] at hP
      exact hP
  use φ, hφ
  intro s
  rw [this, ← MvPolynomial.coe_X, DenseInducing.extend_eq di hψ (MvPolynomial.X s)]
  simp only [AlgHom.mk_coe, MvPolynomial.aeval_X]

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - uniqueness -/
theorem foo_unique {Y : σ → R}
    (hY_pow : ∀ s : σ, Filter.Tendsto (fun n : ℕ => (Y s ^ n)) Filter.atTop (nhds 0))
    (hY_cof : ∀ s : σ, Filter.Tendsto (fun s : σ => (Y s)) Filter.cofinite (nhds 0))
    [τ : UniformSpace R] (ι : Type*) [Nonempty ι] [IsLinearTopology R ι] [CompleteSpace R]
    [T2Space R] (φ : MvPowerSeries σ α →ₐ[α] R) (hφ : Continuous φ)
      (hφ' : ∀ (s : σ), φ (X s) = Y s) :
    φ = (foo α R σ hY_pow hY_cof ι).choose := by
  set ψ := (foo α R σ hY_pow hY_cof ι).choose with hψ
  letI : TopologicalSpace (MvPolynomial σ α) := TopologicalSpace.induced
    MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α)
  haveI di : DenseInducing (@MvPolynomial.toMvPowerSeries σ α _) := {
    induced := rfl
    dense   := by
      rw [DenseRange, Dense]
      sorry }
  have hφψ : ∀ (P : MvPolynomial σ α), φ P = ψ P := by
    intro P
    apply MvPolynomial.induction_on P _ _ _
    · intros a
      rw [MvPolynomial.coe_C]
      sorry
    · intros f g hf hg
      rw [MvPolynomial.coe_add, map_add, map_add, hf, hg]
    · intros f n hf
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hf, hφ',
        (foo α R σ hY_pow hY_cof ι).choose_spec.2]
  ext x
  rw [← DenseInducing.extend_unique di hφψ hφ]


  sorry
