import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic

open scoped TensorProduct

-- The goal is to prove lemma 9 in Roby (1965)
section RingHom

theorem RingHom.ker_eq_ideal_iff {A B : Type _} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) :
    RingHom.ker f = I ↔
      ∃ h : I ≤ RingHom.ker f, Function.Injective (Ideal.Quotient.lift I f h) := by
  constructor
  · intro hI; use le_of_eq hI.symm
    apply RingHom.lift_injective_of_ker_le_ideal
    simp only [hI, le_refl]
  · rintro ⟨hI, h⟩
    simp only [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift f hI,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h
    exact le_antisymm h hI

end RingHom

section AlgHom

theorem AlgHom.ker_eq_ideal_iff {R A B : Type _} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (I : Ideal A) :
    RingHom.ker f = I ↔
      ∃ h : I ≤ RingHom.ker f, Function.Injective (Ideal.Quotient.liftₐ I f h) := by
  have : RingHom.ker f = RingHom.ker f.toRingHom := rfl
  constructor
  · intro hI; use le_of_eq hI.symm
    suffices h : Function.Injective (Ideal.Quotient.lift I f.toRingHom (le_of_eq hI.symm)) by
      intro x y hxy; apply h
      simpa only [Ideal.Quotient.liftₐ_apply] using hxy
    apply RingHom.lift_injective_of_ker_le_ideal
    rw [← hI, ← this]
  · rintro ⟨hI, h⟩
    rw [this]; rw [RingHom.ker_eq_ideal_iff]
    rw [this] at hI ; use hI
    intro x y hxy
    apply h
    simpa only [Ideal.Quotient.liftₐ_apply] using hxy

end AlgHom

variable (R : Type _) [CommRing R] (S : Type _) [CommRing S]

variable (M : Type _) [CommRing M] [Algebra R M] [Algebra S M]
  (N : Type _) [CommRing N] [Algebra R N] [Algebra S N]

variable [Algebra R S] [IsScalarTower R S M]

def kerφ : Ideal (M ⊗[R] N) :=
  Ideal.span ((fun r : S => (r • (1 : M)) ⊗ₜ[R] (1 : N) - (1 : M) ⊗ₜ[R] (r • (1 : N))) '' ⊤)

/-  TODO: when we PR this, ask about why `mkₐ_smul_one_tmul_one` is so slow (and becomes even
  slower inside `ψLeft`.)

  The most general version `mkₐ_smul_one_tmul_one''` is the "correct" one, but it is the
  slowest one inside `ψLeft`.

  Main point: `AlgHom.map_smul` (which we were using before) is deprecated, and `map_smul` is
  much slower.
  -/


--set_option profiler true in
omit [Algebra S N] in
lemma mkₐ_smul_one_tmul_one'' (s : S) {B : Type*} [CommRing B] [Algebra R B]
  [Algebra S B] [IsScalarTower R S B] (f : M ⊗[R] N →ₐ[S] B)  :
    f ((s • (1 : M)) ⊗ₜ[R] (1 : N)) = s • (1 : B ) := by
  suffices (s • (1 : M)) ⊗ₜ[R] (1 : N) = s • (1 : M ⊗[R] N) by
    rw [this, map_smul, map_one]
  rfl

--set_option profiler true in
--set_option trace.Meta.synthInstance true in
lemma mkₐ_smul_one_tmul_one' (s : S) :
    (Ideal.Quotient.mkₐ S (kerφ R S M N)) ((s • (1 : M)) ⊗ₜ[R] (1 : N)) =
      s • (1 : M ⊗[R] N ⧸ kerφ R S M N) := by
  apply mkₐ_smul_one_tmul_one''

omit [Algebra S N] in
lemma mkₐ_smul_one_tmul_one (s : S) (I : Ideal (M ⊗[R] N)) :
    (Ideal.Quotient.mkₐ S I) ((s • (1 : M)) ⊗ₜ[R] (1 : N)) =
      s • (1 : M ⊗[R] N ⧸ I) := by
  suffices (s • (1 : M)) ⊗ₜ[R] (1 : N) = s • (1 : M ⊗[R] N) by
    rw [this, map_smul, map_one]
  rfl

lemma mkₐ_one_tmul_smul_one (s : S) :
    (Ideal.Quotient.mk (kerφ R S M N)) (1 ⊗ₜ[R] (s • 1)) = s • 1 := by
  rw [← (Ideal.Quotient.mk (kerφ R S M N)).map_one, ← Ideal.Quotient.mkₐ_eq_mk S, ← map_smul]
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  apply symm
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span ⟨s, Set.mem_univ s, rfl⟩

variable [IsScalarTower R S N]

-- [tensor_product.compatible_smul R S M N]
open Algebra.TensorProduct TensorProduct

noncomputable def φ : M ⊗[R] N →ₐ[R] M ⊗[S] N :=
  Algebra.TensorProduct.productMap
    Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.restrictScalars R)

theorem φ_apply (m : M) (n : N) : φ R S M N (m ⊗ₜ[R] n) = m ⊗ₜ[S] n := by
  simp only [φ, productMap_apply_tmul, AlgHom.coe_restrictScalars', includeLeft_apply,
    includeRight_apply, tmul_mul_tmul, _root_.mul_one, _root_.one_mul]

theorem φ_surjective : Function.Surjective (φ R S M N) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => use 0; simp only [map_zero]
  | tmul m n => use m ⊗ₜ n; simp only [φ_apply]
  | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩

--set_option profiler true in
-- must be noncomputable, why ?
noncomputable def ψLeft : M →ₐ[S] M ⊗[R] N ⧸ kerφ R S M N := {
  ((Ideal.Quotient.mkₐ S (kerφ R S M N)).restrictScalars R).comp
    Algebra.TensorProduct.includeLeft with
  commutes' := fun s => by
    simp only [AlgHom.toFun_eq_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
      Function.comp_apply, includeLeft_apply, Algebra.algebraMap_eq_smul_one]
    apply mkₐ_smul_one_tmul_one }

-- why is it noncomputable
noncomputable def ψRight : N →ₐ[S] M ⊗[R] N ⧸ kerφ R S M N := {
  (Ideal.Quotient.mkₐ R (kerφ R S M N)).comp includeRight with
  commutes' := fun s => by
    simp only [AlgHom.toFun_eq_coe, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
      Function.comp_apply, includeRight_apply]
    simp only [Algebra.algebraMap_eq_smul_one]
    apply mkₐ_one_tmul_smul_one }

noncomputable def ψ : M ⊗[S] N →ₐ[S] M ⊗[R] N ⧸ kerφ R S M N :=
  productMap (ψLeft R S M N) (ψRight R S M N)

omit [IsScalarTower R S N] in
theorem ψ_apply (m : M) (n : N) :
  ψ R S M N (m ⊗ₜ[S] n) =
    Ideal.Quotient.mk (kerφ R S M N) (m ⊗ₜ[R] n) := by
  simp only [ψ, ψLeft, ψRight, AlgHom.toRingHom_eq_coe, productMap_apply_tmul, AlgHom.coe_mk,
    RingHom.coe_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Ideal.Quotient.mkₐ_eq_mk,
    Function.comp_apply, includeLeft_apply, includeRight_apply]
  rw [← RingHom.map_mul]
  simp only [tmul_mul_tmul, _root_.mul_one, _root_.one_mul]

theorem kerφ_eq : RingHom.ker (φ R S M N).toRingHom = kerφ R S M N := by
  suffices h : kerφ R S M N ≤ RingHom.ker (φ R S M N).toRingHom by
    rw [RingHom.ker_eq_ideal_iff]
    use h
    apply Function.HasLeftInverse.injective
    use ψ R S M N
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [AlgHom.toRingHom_eq_coe, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom]
    induction y using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero, map_zero]
    | tmul m n => simp only [ψ_apply, φ_apply]
    | add x y hx hy =>
      simp only [RingHom.map_add, map_add, ← Ideal.Quotient.mkₐ_eq_mk, hx, hy]
  simp only [kerφ]
  rw [Ideal.span_le]
  intro z hz
  simp only [Set.top_eq_univ, Set.image_univ, Set.mem_range] at hz
  obtain ⟨r, rfl⟩ := hz
  simp only [SetLike.mem_coe, RingHom.sub_mem_ker_iff,AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    φ_apply, TensorProduct.tmul_smul]
  rfl
