/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

-- In PR #15019

import Mathlib.Algebra.MvPolynomial.Equiv

namespace MvPolynomial

section Equiv

variable (R : Type*) [CommSemiring R]

theorem pUnitAlgEquiv_monomial {d : PUnit →₀ ℕ} {r : R} :
    MvPolynomial.pUnitAlgEquiv R (MvPolynomial.monomial d r)
      = Polynomial.monomial (d ()) r := by
  simp [Polynomial.C_mul_X_pow_eq_monomial]

theorem pUnitAlgEquiv_symm_monomial {d : PUnit →₀ ℕ} {r : R} :
    (MvPolynomial.pUnitAlgEquiv R).symm (Polynomial.monomial (d ()) r)
      = MvPolynomial.monomial d r := by
  simp [MvPolynomial.monomial_eq]

end Equiv

section Eval

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

theorem eval₂_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : Unit → S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ a  =
      f.eval₂ φ (a ()) := by
  simp only [MvPolynomial.pUnitAlgEquiv_symm_apply]
  induction f using Polynomial.induction_on' with
  | h_add f g hf hg => simp [hf, hg]
  | h_monomial n r => simp

theorem eval₂_const_pUnitAlgEquiv_symm {f : Polynomial R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R).symm f : MvPolynomial Unit R).eval₂ φ (fun _ ↦ a)  =
      f.eval₂ φ a := by
  rw [eval₂_pUnitAlgEquiv_symm]

theorem eval₂_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : PUnit → S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ (a default) = f.eval₂ φ a := by
  simp only [MvPolynomial.pUnitAlgEquiv_apply]
  induction f using MvPolynomial.induction_on' with
  | monomial d r => simp
  | add f g hf hg => simp [hf, hg]

theorem eval₂_const_pUnitAlgEquiv {f : MvPolynomial PUnit R} {φ : R →+* S} {a : S} :
    ((MvPolynomial.pUnitAlgEquiv R) f : Polynomial R).eval₂ φ a = f.eval₂ φ (fun _ ↦ a) := by
  rw [← eval₂_pUnitAlgEquiv]

end Eval

end MvPolynomial
