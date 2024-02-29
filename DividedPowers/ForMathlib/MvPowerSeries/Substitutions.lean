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

section foo

variable (Y : σ → R)
    (hY_pow : ∀ s : σ, Filter.Tendsto (fun n : ℕ => (Y s ^ n)) Filter.atTop (nhds 0))
    (hY_cof : ∀ _ : σ, Filter.Tendsto (fun s : σ => (Y s)) Filter.cofinite (nhds 0))
    [τ : UniformSpace R]
    [LinearTopology R]
    [CompleteSpace R] [T2Space R]

def foo_ψ : MvPolynomial σ α →ₐ[α] R :=
  { toFun     := fun f => MvPolynomial.aeval Y f
    map_one'  := by simp only [map_one]
    map_mul'  := by simp only [map_mul, forall_const]
    map_zero' := by simp only [map_zero]
    map_add'  := by simp only [map_add, forall_const]
    commutes' := by simp only [AlgHom.commutes, forall_const] }

local instance : TopologicalSpace (MvPolynomial σ α) := TopologicalSpace.induced
    MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α)

-- Suggestion : endow MvPolynomial with the linear topology defined by
-- the “same” Ideal.IsBasis and prove :
def foo_di : DenseInducing (@MvPolynomial.toMvPowerSeries σ α _) := {
  induced := rfl -- there will be something to prove
  dense   := by
    intro f
    rw [mem_closure_iff]
    intro S hSopen hSf
    -- find ideal in the basis such that "f + I ⊆ S"
    -- it will be a monomial , maybe several
    -- f - some truncation of f is a multiple of all of them
    -- just take `trunc f e`
    -- rw [DenseRange, Dense]
    sorry }

lemma foo_ψ_continuous : Continuous (foo_ψ α R σ Y) := by
    rw [continuous_def]
    intros U hU
    sorry

noncomputable def foo_φ : MvPowerSeries σ α →ₐ[α] R :=
  { toFun     := DenseInducing.extend (foo_di α σ) (foo_ψ α R σ Y)
    map_one'  := by rw [← MvPolynomial.coe_one, DenseInducing.extend_eq (foo_di α σ) (foo_ψ_continuous α R σ Y), map_one]
    map_mul'  := by
      simp only [AlgHom.mk_coe]
      sorry
    map_zero' := by
      rw [← MvPolynomial.coe_zero]
      simp only [AlgHom.mk_coe]
      erw [DenseInducing.extend_eq (foo_di α σ) (foo_ψ_continuous α R σ Y), map_zero]
    map_add'  := sorry
    commutes' := sorry }

theorem foo_φ_coe :
    foo_φ α R σ Y = DenseInducing.extend (foo_di α σ)  (foo_ψ α R σ Y) := rfl

theorem foo_Continuous_φ : Continuous (foo_φ α R σ Y) := by
  rw [foo_φ_coe]
  apply DenseInducing.continuous_extend (foo_di α σ)
  intro f
  use (foo_φ α R σ Y f)
  rw [tendsto_nhds]
  intros U hUopen hUf
  rw [Filter.mem_comap]
  use (foo_φ α R σ Y ⁻¹' U)
  constructor
  · rw [mem_nhds_iff]
    have := MvPolynomial.toMvPowerSeries ⁻¹' (⇑(foo_φ α R σ Y) ⁻¹' U)
    sorry
  · intro P hP
    rw [Set.mem_preimage, foo_φ_coe, Set.mem_preimage,
      DenseInducing.extend_eq _ (foo_ψ_continuous α R σ Y)] at hP
    exact hP

theorem foo_φ_apply_X (s : σ) : (foo_φ α R σ Y) (X s) = Y s := by
  rw [foo_φ_coe, ← MvPolynomial.coe_X,
    DenseInducing.extend_eq _ (foo_ψ_continuous _ _ _ _ ) (MvPolynomial.X s)]
  simp only [foo_ψ, AlgHom.mk_coe, MvPolynomial.aeval_X]

variable {Y}

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - Existence -/
theorem foo :
    ∃ (φ : MvPowerSeries σ α →ₐ[α] R) (_ : Continuous φ), ∀ (s : σ), φ (X s) = Y s := by
  use foo_φ α R σ Y, foo_Continuous_φ α R σ Y, fun s ↦ foo_φ_apply_X α R σ Y s


/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - uniqueness -/
theorem foo_unique (φ : MvPowerSeries σ α →ₐ[α] R) (hφ : Continuous φ)
      (hφ' : ∀ (s : σ), φ (X s) = Y s) (f : MvPowerSeries σ α) :
    φ f = foo_φ α R σ Y f := by
  sorry
 /-
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
-/


end foo
