/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! # An equivalence for `Fin 2`. -/
section Fin2

variable (X : Type*) [Zero X]

/-- The space of finitely supported functions `Fin 2 →₀ α` is equivalent to `α × α`.
See also `finTwoArrowEquiv` in Mathlib. -/
@[simps -fullyApplied]
noncomputable def finTwoArrowEquiv' : (Fin 2 →₀ X) ≃ (X × X) where
  toFun x     := (x 0, x 1)
  invFun x    := Finsupp.ofSupportFinite ![x.1, x.2] (Set.toFinite _)
  left_inv x  := by
    simp only [Fin.isValue, Finsupp.ext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  right_inv x := rfl

theorem finTwoArrowEquiv'_sum_eq {d : ℕ × ℕ}  :
    (((finTwoArrowEquiv' ℕ).symm d).sum fun _ n ↦ n) = d.1 + d.2 := by
  simp [Finsupp.sum, finTwoArrowEquiv'_symm_apply, Finsupp.ofSupportFinite_coe]
  rw [Finset.sum_subset (Finset.subset_univ _)
    (fun _ _ h ↦ by simpa [Finsupp.ofSupportFinite_coe] using h)]
  simp [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

theorem Finsupp.ofSupportFinite_fin_two_eq (n : Fin 2 →₀ ℕ) :
    Finsupp.ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

end Fin2
