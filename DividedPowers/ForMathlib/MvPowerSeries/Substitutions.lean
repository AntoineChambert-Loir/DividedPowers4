import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology

import Mathlib.Data.MvPolynomial.CommRing
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc

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

section

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

end
namespace MvPolynomial

open Set
section Ideals

variable (α : Type*) [CommRing α]

def basis' : (σ →₀ ℕ) → Ideal (MvPolynomial σ α) := fun d =>
  Ideal.span {MvPolynomial.monomial d 1}

/-- The underlying family for the `Ideal.IsBasis` in a multivariate power series ring. -/
def basis : (σ →₀ ℕ) → Ideal (MvPolynomial σ α) := fun d =>
  { carrier   := {f | ∀ e ≤ d, coeff e f = 0} -- monomial e 1 ∣ f
    zero_mem' := fun e _ => by rw [coeff_zero]
    add_mem'  := fun hf hg e he => by rw [coeff_add, hf e he, hg e he, add_zero]
    smul_mem' := fun f g hg e he => by
      classical
      rw [smul_eq_mul, coeff_mul]
      apply Finset.sum_eq_zero
      rintro uv huv
      convert MulZeroClass.mul_zero (coeff uv.fst f)
      exact hg  _ (le_trans (le_iff_exists_add'.mpr
        ⟨uv.fst, (Finset.mem_antidiagonal.mp huv).symm⟩) he) }

/-- A power series `f` belongs to the ideal `basis σ α d` if and only if `coeff α e f = 0` for all
  `e ≤ d`.  -/
theorem mem_basis (f : MvPolynomial σ α) (d : σ →₀ ℕ) :
    f ∈ basis σ α d ↔ ∀ e ≤ d, coeff e f = 0 := by
  simp only [basis, Submodule.mem_mk, AddSubmonoid.mem_mk, Set.mem_setOf_eq]
  rfl

/-- If `e ≤ d`, then we have the inclusion of ideals `basis σ α d ≤ basis σ α e`. -/
theorem basis_le {e d : σ →₀ ℕ} (hed : e ≤ d) : basis σ α d ≤ basis σ α e :=
  fun _ => forall_imp (fun _ h ha => h (le_trans ha hed))

/-- `basis σ α d ≤ basis σ α e` if and only if `e ≤ d`.-/
theorem basis_le_iff [Nontrivial α] (d e : σ →₀ ℕ) :
    basis σ α d ≤ basis σ α e ↔ e ≤ d := by
  classical
  refine' ⟨_, basis_le _ _⟩
  simp only [basis, Submodule.mk_le_mk, AddSubmonoid.mk_le_mk, setOf_subset_setOf]
  intro h
  rw [← inf_eq_right]
  apply le_antisymm
  . exact inf_le_right
  . by_contra h'
    simp only [AddSubsemigroup.mk_le_mk, setOf_subset_setOf] at h
    specialize h (monomial e 1) _
    . intro e' he'
      simp only [coeff_monomial, ite_eq_right_iff, one_ne_zero, imp_false, ne_eq]
      intro hee'
      rw [← hee'] at he'
      apply h'
      exact le_inf_iff.mpr ⟨he', le_rfl⟩
    apply one_ne_zero' α
    convert h e le_rfl
    simp only [coeff_monomial, ↓reduceIte]

/-- The function `basis σ α` is antitone. -/
theorem basis_antitone : Antitone (basis σ α) := fun _ _ h => basis_le σ α h

-- TODO : generalize to [Ring α]
/-- `MvPowerSeries.basis` is an `Ideal.IsBasis`. -/
theorem idealIsBasis : @Ideal.IsBasis (MvPolynomial σ α) _ _ (basis σ α) :=
  Ideal.IsBasis.ofComm fun d e => by use d ⊔ e; apply Antitone.map_sup_le (basis_antitone σ α)

/-- `MvPowerSeries.basis` is a `RingSubgroupsBasis`. -/
theorem toRingSubgroupsBasis : RingSubgroupsBasis fun d => (basis σ α d).toAddSubgroup :=
  (idealIsBasis σ α).toRingSubgroupsBasis

end Ideals

end MvPolynomial


section foo

namespace MvPolynomial

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

local instance topologicalSpace : TopologicalSpace (MvPolynomial σ α) :=
  (idealIsBasis σ α).topology
  --TopologicalSpace.induced MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α

/-- The ring topology on MvPolynomial of a topological ring -/
theorem topologicalRing : @TopologicalRing (MvPolynomial σ α) (idealIsBasis σ α).topology _ :=
  (idealIsBasis σ α).to_topologicalRing


-- NOTE (MI): I am having trouble with this proof because of the `FunLike` hypothesis in
-- `Inducing.continuousAdd` and similar lemmas
/-- The induced ring topology on MvPolynomial of a topological ring -/
theorem induced_topologicalRing : @TopologicalRing (MvPolynomial σ α)
    (TopologicalSpace.induced MvPolynomial.toMvPowerSeries (MvPowerSeries.topologicalSpace σ α))
     _ :=
  letI τ := (TopologicalSpace.induced MvPolynomial.toMvPowerSeries
    (MvPowerSeries.topologicalSpace σ α))
  { continuous_add := by
      have h : ContinuousAdd (MvPolynomial σ α) := by
        --apply @Inducing.continuousAdd (MvPolynomial σ α) (MvPowerSeries σ α)
          --((MvPolynomial σ α) → (MvPowerSeries σ α))
        sorry
      exact h.continuous_add
      --apply Inducing.continuousAdd
      --continuousAdd_induced MvPolynomial.toMvPowerSeries
    continuous_mul := sorry
    continuous_neg := sorry }

-- Suggestion : endow MvPolynomial with the linear topology defined by
-- the “same” Ideal.IsBasis and prove :
def foo_di : DenseInducing (@MvPolynomial.toMvPowerSeries σ α _) := {
  induced := by
    let τ := MvPolynomial.topologicalSpace α σ
    let τ' := TopologicalSpace.induced toMvPowerSeries (MvPowerSeries.topologicalSpace σ α)
    rw [TopologicalSpace.eq_iff_nhds_eq]
    suffices ∀ s, s ∈ @nhds _ τ 0 ↔ s ∈ @nhds _ τ' 0 by
    -- mv nhds from 0 to a
      intros S f _hfS -- _hfS is never used
      rw [← add_zero f, @mem_nhds_add_iff _ _ τ,
        @mem_nhds_add_iff _ _ τ' (induced_topologicalRing α σ).to_topologicalAddGroup]
      exact this _
    -- Nhds of zero agree
    intro S
    rw [(RingSubgroupsBasis.hasBasis_nhds (toRingSubgroupsBasis σ α) 0).mem_iff, mem_nhds_induced]
    simp only [sub_zero, Submodule.mem_toAddSubgroup, true_and, coe_zero]
    constructor
    · rintro ⟨i, hi⟩
      use {b | b ∈ MvPowerSeries.basis σ α i}
      exact ⟨(MvPowerSeries.mem_nhds_zero_iff σ α _).mpr ⟨i, by exact fun ⦃a⦄ a => a⟩, hi⟩
    · rintro ⟨U, hU0, hUS⟩
      rw [MvPowerSeries.mem_nhds_zero_iff] at hU0
      obtain ⟨i, hi⟩ := hU0
      use i
      apply le_trans _ hUS
      simp only [Set.le_eq_subset]
      have hi' : toMvPowerSeries ⁻¹' {b | b ∈ MvPowerSeries.basis σ α i} =
        {b | b ∈ basis σ α i} := rfl
      rw [← hi']
      exact Set.preimage_mono hi
  dense   := by
    intro f
    rw [mem_closure_iff]
    intro S hSopen hSf
    have hS : ∃ i, {f + b | b ∈ MvPowerSeries.basis σ α i} ⊆ S := by
      let τ := MvPowerSeries.topologicalSpace σ α
      letI tg := @TopologicalRing.to_topologicalAddGroup _ _ τ (MvPowerSeries.topologicalRing σ α)
      rw [isOpen_iff_mem_nhds] at hSopen
      specialize hSopen _ hSf
      rw [← add_zero f, mem_nhds_add_iff, MvPowerSeries.mem_nhds_zero_iff] at hSopen
      obtain ⟨i, hi⟩ := hSopen
      use i
      intro x ⟨b, hb, hbx⟩
      rw [← hbx]
      exact hi hb
    obtain ⟨i, hi⟩ := hS
    rw [Set.inter_nonempty]
    use MvPowerSeries.trunc' _ i f
    constructor
    · apply hi
      use (- f + (MvPowerSeries.trunc' _ i f))
      constructor
      · simp only [MvPowerSeries.basis, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq, map_add, map_neg, coeff_coe]
        intros e hei
        rw [MvPowerSeries.coeff_trunc', if_pos hei, add_left_neg]
      · simp only [add_neg_cancel_left]
    · simp only [Set.mem_range, coe_inj, exists_eq] }

lemma foo_ψ_continuous : Continuous (foo_ψ α R σ Y) := by
    rw [continuous_def]
    intros U hU
    rw [isOpen_iff_mem_nhds]
    intros f hf
    rw [foo_ψ]
    simp only [AlgHom.mk_coe]
    sorry

noncomputable def foo_φ : MvPowerSeries σ α →ₐ[α] R :=
  { toFun     := DenseInducing.extend (foo_di α σ) (foo_ψ α R σ Y)
    map_one'  := by rw [← MvPolynomial.coe_one, DenseInducing.extend_eq (foo_di α σ)
      (foo_ψ_continuous α R σ Y), map_one]
    map_zero' := by
      rw [← MvPolynomial.coe_zero]
      simp only [AlgHom.mk_coe]
      erw [DenseInducing.extend_eq (foo_di α σ) (foo_ψ_continuous α R σ Y), map_zero]
    map_mul'  := fun f g => by
      /- set p : (MvPowerSeries σ α) → (MvPowerSeries σ α) → Prop := fun f g =>
        DenseInducing.extend (foo_di α σ) (⇑(foo_ψ α R σ Y)) (f * g) =
          DenseInducing.extend (foo_di α σ) (⇑(foo_ψ α R σ Y)) f *
          DenseInducing.extend (foo_di α σ) (⇑(foo_ψ α R σ Y)) g with hp -/
      --simp only [AlgHom.mk_coe]
      apply @DenseRange.induction_on₂ (MvPolynomial σ α) (MvPowerSeries σ α) _
        (@MvPolynomial.toMvPowerSeries σ α _) _ (foo_di α σ).dense _ _ f g
      · /- let τ := MvPowerSeries.topologicalSpace σ α
        have tg := @TopologicalRing.to_topologicalAddGroup _ _ τ (MvPowerSeries.topologicalRing σ α)
        rw [← isOpen_compl_iff]
        rw [isOpen_iff_mem_nhds]
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Prod.forall]
        intros a b hab
        rw [← add_zero (a, b), mem_nhds_add_iff, Prod.zero_eq_mk]  -/
        sorry
      · intro a b
        rw [← coe_mul]
        simp only [DenseInducing.extend_eq (foo_di α σ) (foo_ψ_continuous α _ σ _), map_mul]

    map_add'  := sorry
    commutes' := fun r => by
      have h : ((algebraMap α (MvPowerSeries σ α)) r) = ((algebraMap α (MvPolynomial σ α)) r) := by
        rw [MvPowerSeries.algebraMap_apply]
        rw [MvPolynomial.algebraMap_apply]
        simp only [Algebra.id.map_eq_id, RingHom.id_apply, coe_C]
      simp only [h, DenseInducing.extend_eq (foo_di α σ) (foo_ψ_continuous α _ σ _)]
      simp only [foo_ψ, AlgHom.mk_coe, AlgHom.commutes] }

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

theorem foo_φ_apply_X (s : σ) : (foo_φ α R σ Y) (MvPowerSeries.X s) = Y s := by
  rw [foo_φ_coe, ← MvPolynomial.coe_X,
    DenseInducing.extend_eq _ (foo_ψ_continuous _ _ _ _ ) (MvPolynomial.X s)]
  simp only [foo_ψ, AlgHom.mk_coe, MvPolynomial.aeval_X]

variable {Y}

/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - Existence -/
theorem foo :
    ∃ (φ : MvPowerSeries σ α →ₐ[α] R) (_ : Continuous φ), ∀ (s : σ), φ (MvPowerSeries.X s) = Y s := by
  use foo_φ α R σ Y, foo_Continuous_φ α R σ Y, fun s ↦ foo_φ_apply_X α R σ Y s


/-- Bourbaki, Algèbre, chap. 4, §4, n°3, Prop. 4 (ii) - uniqueness -/
theorem foo_unique (φ : MvPowerSeries σ α →ₐ[α] R) (hφ : Continuous φ)
      (hφ' : ∀ (s : σ), φ (MvPowerSeries.X s) = Y s) (f : MvPowerSeries σ α) :
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

end MvPolynomial

end foo
