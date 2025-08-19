import Mathlib.Algebra.BigOperators.Finsupp.Fin

section Fin2

variable (X : Type*) [Zero X]

noncomputable def finTwoArrowEquiv' : (Fin 2 →₀ X) ≃ (X × X) where
  toFun x     := (x 0, x 1)
  invFun x    := Finsupp.ofSupportFinite ![x.1, x.2] (Set.toFinite _)
  left_inv x  := by
    simp only [Fin.isValue, Finsupp.ext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  right_inv x := rfl

end Fin2
