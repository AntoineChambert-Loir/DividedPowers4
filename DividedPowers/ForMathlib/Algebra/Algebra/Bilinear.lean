import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace TensorProduct

open scoped TensorProduct

open LinearMap Finsupp

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-[Mathlib.RingTheory.PolynomialLaw.Basic, Mathlib.LinearAlgebra.DirectSum.TensorProduct,
Mathlib.Algebra.Algebra.Operations, Mathlib.LinearAlgebra.TensorProduct.DirectLimit]-/
lemma exists_Finsupp (S : Type*) [CommSemiring S] [Algebra R S] (μ : S ⊗[R] M) :
    ∃ (m : S →₀ M), μ = m.sum (fun s x => s ⊗ₜ[R] x) := by
  classical
  induction μ using TensorProduct.induction_on with
  | zero => use 0; rw [sum_zero_index]
  | tmul s m => use single s m; simp only [tmul_zero, sum_single_index]
  | add x y hx hy =>
    obtain ⟨sx, rfl⟩ := hx
    obtain ⟨sy, rfl⟩ := hy
    use sx + sy
    rw [sum_add_index (fun _ ↦ by simp) (fun _ _ _ _ ↦ by rw [TensorProduct.tmul_add])]

/- [Mathlib.RingTheory.PolynomialLaw.Basic, Mathlib.LinearAlgebra.DirectSum.TensorProduct,
 Mathlib.Algebra.Algebra.Operations, Mathlib.LinearAlgebra.TensorProduct.DirectLimit]-/
theorem exists_Fin (S : Type*) [CommSemiring S] [Algebra R S] (sm : S ⊗[R] M) :
    ∃ (n : ℕ) (s : Fin n → S) (m : Fin n → M),
      sm = Finset.univ.sum (fun i ↦ (s i) ⊗ₜ[R] (m i)) := by
  obtain ⟨m, rfl⟩ := TensorProduct.exists_Finsupp S sm
  let e : m.support ≃ Fin (m.support.card) := Finset.equivFin _
  use m.support.card, fun i ↦ e.symm i, fun i ↦ m (e.symm i)
  rw [sum, ← Finset.sum_attach]
  apply Finset.sum_equiv e
  simp only [Finset.mem_attach, Finset.mem_univ, implies_true]
  intros; simp only [Equiv.symm_apply_apply]

-- Mathlib.Algebra.Algebra.Bilinear
lemma smul_rTensor {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    {S : Type*} [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T) (s : S) (m : S ⊗[R] M) :
    φ s • (φ.toLinearMap.rTensor M m) = φ.toLinearMap.rTensor M (s • m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul s' m =>
    simp only [rTensor_tmul, AlgHom.toLinearMap_apply, smul_tmul', smul_eq_mul, _root_.map_mul]
  | add m m' hm hm' => simp only [map_add, smul_add, hm, hm']

variable {R : Type*} [CommSemiring R]
  {S : Type*} [Semiring S] [Algebra R S]
  {M : Type*} [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  {P : Type*} [AddCommMonoid P] [Module R P]
  {Q : Type*} [AddCommMonoid Q] [Module R Q]

/- [Mathlib.LinearAlgebra.TensorProduct.Associator, Mathlib.Algebra.Algebra.Bilinear,
DividedPowers.ForMathlib.Algebra.Algebra.Bilinear, Mathlib.LinearAlgebra.TensorProduct.DirectLimit]-/
/-- If `f` is `S`-linear, then `TensorProduct.map (f.restrictScalars R) g` is `S`-linear -/
lemma map_isLinearMap_of_left (f : M →ₗ[S] N) (g : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (f.restrictScalars R) g) where
  map_add  x y := by rw [map_add]
  map_smul c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul x y => simp only [smul_tmul', map_tmul, coe_restrictScalars, map_smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

lemma rTensor_smul' (f : M →ₗ[S] N) (s : S) (t : M ⊗[R] P) :
    rTensor P (f.restrictScalars R) (s • t) = s • (rTensor P (f.restrictScalars R) t) := by
  have : rTensor P (f.restrictScalars R) = (IsLinearMap.mk' _
    (TensorProduct.map_isLinearMap_of_left f LinearMap.id)).restrictScalars R := rfl
  rw [this, coe_restrictScalars, map_smul, IsLinearMap.mk'_apply]

end TensorProduct

open TensorProduct

namespace Submodule

/- Mathlib.LinearAlgebra.TensorProduct.Associator,
 Mathlib.Algebra.Algebra.Bilinear,
 Mathlib.LinearAlgebra.TensorProduct.DirectLimit]-/
theorem span_tensorProduct_eq_top_of_span_eq_top {R σ M S : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M]
    [Semiring S] [Algebra R S] (e : σ → M) (hm : span R (Set.range e) = ⊤) :
    (span S (Set.range fun s ↦ (1 : S) ⊗ₜ[R] e s) : Submodule S (S ⊗[R] M)) = ⊤ := by
  rw [eq_top_iff]
  intro m h
  induction m using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul r m =>
      let f : M →ₗ[R] S ⊗[R] M :=
        { toFun m       := (1 : S) ⊗ₜ[R] m
          map_add' x y  := by simp [tmul_add]
          map_smul' a x := by simp [tmul_smul] }
      suffices r ⊗ₜ[R] m = r • (1 : S) ⊗ₜ[R] m by
        have heq : (Set.range fun s ↦ 1 ⊗ₜ[R] e s) = ⇑f '' Set.range e := by
          conv_rhs => rw [← Set.image_univ, Set.image_image, Set.image_univ]
          simp [f]
        exact this ▸ smul_mem _ r (span_le_restrictScalars R _ _
          (heq ▸ apply_mem_span_image_of_mem_span f (hm ▸ mem_top)))
      rw [smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => exact Submodule.add_mem _ (hx mem_top) (hy mem_top)

end Submodule
