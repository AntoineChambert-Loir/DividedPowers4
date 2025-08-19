import Mathlib.Algebra.BigOperators.Finsupp.Fin

section Fin2

variable (X : Type*) [Zero X]

/- **MI**: I added the simp lemmas for compatibility with Mathlib's `finTwoArrowEquiv`, but
  I am not convinced they are a good idea. -/

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

end Fin2
