/- copyright ACL @ MIdFF 2024 -/

import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Augmentation ideals

This is tentative

probably the subalgebra / section should be data
rather than Prop valued existence statements

 -/

variable (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A)

namespace Ideal

open AlgHom RingHom Submodule Ideal.Quotient

open TensorProduct

/-- An ideal J of a commutative ring A is an augmentation ideal
if `Ideal.Quotient.mk J` has a right inverse which is a `RingHom` -/
def IsAugmentation : Prop :=
  ∃ g : A ⧸ J →+* A, Function.RightInverse g (Ideal.Quotient.mk J)

/-- An ideal `J` of a commutative `R`-algebra `A` is an augmentation ideal
if `Ideal.Quotient.mkₐ R J` has a right inverse which is an `AlgHom` -/
def IsAugmentationₐ (R : Type*) [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A] (J : Ideal A) : Prop :=
  ∃ g : A ⧸ J →ₐ[R] A, Function.RightInverse g (Ideal.Quotient.mkₐ R J)

theorem isAugmentationₐ_iff :
    J.IsAugmentationₐ R ↔
    ∃ (A₀ : Subalgebra R A), IsCompl (Subalgebra.toSubmodule A₀) (Submodule.restrictScalars R J) := by
  constructor
  · rintro ⟨f, hf⟩
    use f.range
    apply IsCompl.mk
    · rw [Submodule.disjoint_def]
      rintro x ⟨y, rfl⟩
      simp only [toRingHom_eq_coe, coe_coe, restrictScalars_mem]
      intro hy
      rw [← hf y, mkₐ_eq_mk]
      convert AlgHom.map_zero _
      rw [← mem_ker, mk_ker]
      exact hy
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have : x = f (mkₐ R J x) + (x - f (mkₐ R J x)) := by ring
      rw [this]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_left
        simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range, exists_apply_eq_apply]
      · apply Submodule.mem_sup_right
        simp only [Submodule.restrictScalars_mem]
        suffices x - f x ∈ ker (mkₐ R J) by
          convert this
          exact mk_ker.symm
        rw [mem_ker, map_sub, ← mkₐ_eq_mk R, hf, sub_self]
  · rintro ⟨A₀, ⟨hd, hc⟩⟩
    let u : A₀ →ₐ[R] A ⧸ J := (Ideal.Quotient.mkₐ R J).comp (Subalgebra.val A₀)
    suffices hu : Function.Bijective u by
      let u' : A₀ ≃ₐ[R] A ⧸ J := AlgEquiv.ofBijective u hu
      use (Subalgebra.val A₀).comp u'.symm
      rintro x
      rcases hu.surjective x with ⟨y, rfl⟩
      simp only [AlgHom.coe_comp, Subalgebra.coe_val, AlgHom.coe_coe, Function.comp_apply]
      -- Something like AlgEquiv.symm_apply_eq is missing
      suffices u y = u' y by
        rw [this]
        rw [AlgEquiv.leftInverse_symm]
        simp only [AlgEquiv.coe_ofBijective, AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val,
          Function.comp_apply, u', u]
      simp only [AlgEquiv.coe_ofBijective, u']
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x
      simp only [RingHom.mem_ker, mem_bot]
      simp only [Submodule.disjoint_def] at hd
      specialize hd x x.property
      simp only [Submodule.restrictScalars_mem, ZeroMemClass.coe_eq_zero] at hd
      intro hx
      apply hd
      simpa only [AlgHom.coe_comp, mkₐ_eq_mk, Subalgebra.coe_val, Function.comp_apply, u, ← RingHom.mem_ker, mk_ker] using hx
    · -- missing RingHomClass argument for RingHom.range_top_iff_surjective
      intro x
      rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
      simp only [codisjoint_iff, eq_top_iff] at hc
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp (hc (show x ∈ ⊤ by exact trivial))
      use ⟨x, hx⟩
      rw [map_add]
      convert (add_zero _).symm
      rwa [← RingHom.mem_ker, mk_ker]

/-- If J is an `R`-algebra augmentation ideal, then S ⊗[R] J
  is a `S`-algebra augmentation ideal -/
theorem IsAugmentationₐ.baseChange
    (hJ : J.IsAugmentationₐ R)
    (S : Type*) [CommRing S] [Algebra R S] [Algebra A S] [IsScalarTower R A S] :
    Ideal.IsAugmentationₐ S (J.map Algebra.TensorProduct.includeRight : Ideal (S ⊗[R] A)) := by
  obtain ⟨f, hf⟩ := hJ
  have that : RingHom.ker (mkₐ R J) = J := mkₐ_ker R J
  let g : S ⊗[R] A ⧸ (Ideal.map Algebra.TensorProduct.includeRight J : Ideal (S ⊗[R] A)) →ₐ[S] S ⊗[R] (A ⧸ J) := {
    toRingHom := by
      apply Quotient.lift (Ideal.map Algebra.TensorProduct.includeRight J)
        ((Algebra.TensorProduct.map (AlgHom.id R S) (mkₐ R J)))
      intro a ha
      rwa [← that, ← Algebra.TensorProduct.lTensor_ker _ (mkₐ_surjective R J), mem_ker] at ha
    commutes' := fun s ↦ by
      have : algebraMap S ((S ⊗[R] A) ⧸ (map Algebra.TensorProduct.includeRight J : Ideal (S ⊗[R] A))) s = mkₐ S _ (s ⊗ₜ[R] 1) := by
        rw [mkₐ_eq_mk, ← mk_algebraMap, Algebra.TensorProduct.algebraMap_apply,
          Algebra.id.map_eq_self]
      simp [this] }
  -- let g := Ideal.kerLiftAlg (Algebra.TensorProduct.map (AlgHom.id A S) (mkₐ A I))
  -- rw [Algebra.TensorProduct.lTensor_ker _ (mkₐ_surjective A I), that] at g
  -- it seems unusable
  let g' : S ⊗[R] (A ⧸ J) →ₐ[S] S ⊗[R] A := Algebra.TensorProduct.map (AlgHom.id S S) f
  use g'.comp g
  intro x
  rcases mkₐ_surjective A _ x with ⟨x, rfl⟩
  simp only [mkₐ_eq_mk, AlgHom.coe_mk, coe_coe, AlgHom.coe_comp, Function.comp_apply, liftₐ_apply,
    Quotient.lift_mk, g]
  induction x using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul s r =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, mkₐ_eq_mk, g'] --  hf r]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← TensorProduct.tmul_sub]
    rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul']
    rw [← algebraMap_smul (S ⊗[R] A), smul_eq_mul]
    apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem (Algebra.TensorProduct.includeRight)
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    apply hf
  | add x y hx hy => simp only [map_add, hx, hy]
