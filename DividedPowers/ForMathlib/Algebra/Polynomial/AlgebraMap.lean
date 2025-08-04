/- Copyright ACL & MIdFF 2024 -/

import Mathlib.Algebra.Polynomial.AlgebraMap

namespace Polynomial

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]
  {S' : Type*} [CommSemiring S'] [Algebra R S']

lemma C_eq_algebraMap' (r : R) : C (algebraMap R S r) = algebraMap R S[X] r := rfl

-- Mathlib.Algebra.Polynomial.AlgebraMap
/-- baseChange φ aplies φ on the coefficients of a polynomial in S[X] -/
noncomputable def baseChange (φ : S →ₐ[R] S') : S[X] →ₐ[R] S'[X] where
  toRingHom := eval₂RingHom (C.comp φ) X
  commutes' := fun r ↦ by simp

lemma coeff_baseChange_apply (φ : S →ₐ[R] S') (f : S[X]) (p : ℕ) :
    coeff (baseChange φ f) p = φ (coeff f p) := by
  rw [baseChange, AlgHom.coe_mk, coe_eval₂RingHom]
  induction f using Polynomial.induction_on with
  | C r =>
    simp only [eval₂_C, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, coeff_C,
      apply_ite φ, map_zero]
  | add f g hf hg => simp only [eval₂_add, coeff_add, hf, hg, map_add]
  | monomial n r _ =>
    simp only [eval₂_mul, eval₂_C, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      eval₂_X_pow, coeff_C_mul, _root_.map_mul, coeff_X_pow, apply_ite φ, _root_.map_one, map_zero]

lemma lcoeff_comp_baseChange_eq (φ : S →ₐ[R] S') (p : ℕ) :
    LinearMap.comp (AlgHom.toLinearMap φ) ((lcoeff S p).restrictScalars R) =
      LinearMap.comp ((lcoeff S' p).restrictScalars R) (baseChange φ).toLinearMap := by
  ext f
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, lcoeff_apply,
    AlgHom.toLinearMap_apply, coeff_baseChange_apply]

-- Mathlib.Algebra.Polynomial.AlgebraMap
lemma baseChange_monomial (φ : S →ₐ[R] S') (n : ℕ) (a : S) :
    (baseChange φ) ((Polynomial.monomial n) a) = (Polynomial.monomial n) (φ a) := by
  simp only [baseChange, AlgHom.coe_mk, coe_eval₂RingHom, eval₂_monomial, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, C_mul_X_pow_eq_monomial]

end Polynomial
