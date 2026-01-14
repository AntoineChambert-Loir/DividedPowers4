/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Linear algebra of tensor products -/

namespace TensorProduct

open scoped TensorProduct

open LinearMap Finsupp

variable {R S M : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M]

/-- Any `μ : S ⊗[R] M` can be written as a sum of basic tensors indexed by a finitely
  supported function `m : S →₀ M`. -/
lemma exists_Finsupp (μ : S ⊗[R] M) : ∃ (m : S →₀ M), μ = m.sum (fun s x => s ⊗ₜ[R] x) := by
  classical
  induction μ using TensorProduct.induction_on with
  | zero => use 0; rw [sum_zero_index]
  | tmul s m => use single s m; simp only [tmul_zero, sum_single_index]
  | add x y hx hy =>
    obtain ⟨sx, rfl⟩ := hx
    obtain ⟨sy, rfl⟩ := hy
    use sx + sy
    rw [sum_add_index (fun _ ↦ by simp) (fun _ _ _ _ ↦ by rw [TensorProduct.tmul_add])]

/-- Any `μ : S ⊗[R] M` can be written as a sum of basic tensors indexed over some `Fin n`. -/
theorem exists_Fin  (sm : S ⊗[R] M) :
    ∃ (n : ℕ) (s : Fin n → S) (m : Fin n → M),
      sm = Finset.univ.sum (fun i ↦ (s i) ⊗ₜ[R] (m i)) := by
  obtain ⟨m, rfl⟩ := TensorProduct.exists_Finsupp sm
  let e : m.support ≃ Fin (m.support.card) := Finset.equivFin _
  use m.support.card, fun i ↦ e.symm i, fun i ↦ m (e.symm i)
  rw [sum, ← Finset.sum_attach]
  apply Finset.sum_equiv e
  simp only [Finset.mem_attach, Finset.mem_univ, implies_true]
  intros; simp only [Equiv.symm_apply_apply]

lemma rTensor_smul {T : Type*} [Semiring T] [Algebra R T] (φ : S →ₐ[R] T) (s : S) (m : S ⊗[R] M) :
    φ.toLinearMap.rTensor M (s • m) = φ s • (φ.toLinearMap.rTensor M m)  := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul s' m =>
    simp only [rTensor_tmul, AlgHom.toLinearMap_apply, smul_tmul', smul_eq_mul, _root_.map_mul]
  | add m m' hm hm' => simp only [map_add, smul_add, hm, hm']

variable {N P Q : Type*} [Module S M] [IsScalarTower R S M] [AddCommMonoid N] [Module R N]
  [Module S N] [IsScalarTower R S N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

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

/-- If `e : σ → M` is such that `Set.range e` generates `M` as an `R`-module, then
  `Set.range fun s ↦ (1 : S) ⊗ₜ[R] e s` generates `S ⊗[R] M` as an `S`-module. -/
theorem span_tensorProduct_eq_top_of_span_eq_top {R σ M S : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [Semiring S] [Algebra R S] {e : σ → M}
    (hm : span R (Set.range e) = ⊤) :
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

/-- If `R` is nontrivial, so is any `R`-algebra `S`. -/
theorem Algebra.not_nontrivial_of_not_nontrivial (R S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] (hR : ¬ Nontrivial R) : ¬ Nontrivial S := by
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  have hs (s : S) : s = 0 := by
    rw [← mul_one s, ← map_one (algebraMap R S), hR 1 0, map_zero, mul_zero]
  intro s t
  rw [hs s, hs t]

/-- If `S` is nontrivial, so is `S ⊗[R] M`. -/
theorem TensorProduct.not_nontrivial_of_not_nontrivial (R S M : Type*) [CommSemiring R]
    [AddCommMonoid M] [Module R M] [CommSemiring S] [Algebra R S] (hS : ¬ Nontrivial S) :
    ¬ Nontrivial (S ⊗[R] M) := by
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  have h (sm : S ⊗[R] M) : sm = 0 := by
    rw [← _root_.one_smul S sm, hS 1 0, _root_.zero_smul]
  intro sm sm'
  rw [h sm, h sm']

section

variable {R S S' : Type*} [CommSemiring R] [Semiring S] [Semiring S']
  [Algebra R S] [Algebra R S']

--theorem Subalgebra.val_comp_inclusion {A B : Subalgebra R S} (h : A ≤ B) :
 -- (Subalgebra.val B).comp (Subalgebra.inclusion h) = Subalgebra.val A := rfl

variable (R S) in
/-- `algebraMap R S` as an `AlgHom`. -/
def Algebra.toAlgHom :
    R →ₐ[R] S where
  toRingHom := algebraMap R S
  commutes' := fun _ ↦ rfl

theorem AlgEquiv.self_trans_symm_eq_refl (e : S ≃ₐ[R] S') :
  e.trans e.symm = AlgEquiv.refl := by aesop

theorem AlgEquiv.symm_trans_self_eq_refl (e : S ≃ₐ[R] S') :
  e.symm.trans e = AlgEquiv.refl := by
  aesop

end
