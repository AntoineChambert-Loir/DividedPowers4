/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Base change of polynomial maps (mapAlgHom)

-/

-- In PR #30547
namespace Polynomial


variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]
  {S' : Type*} [CommSemiring S'] [Algebra R S']

/-
lemma coeff_mapAlgHom_apply (φ : S →ₐ[R] S') (f : S[X]) (p : ℕ) :
    coeff (mapAlgHom φ f) p = φ (coeff f p) := by
  simp only [mapAlgHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, coe_mapRingHom, coeff_map,
    RingHom.coe_coe]

lemma lcoeff_comp_mapAlgHom_eq (φ : S →ₐ[R] S') (p : ℕ) :
    LinearMap.comp (AlgHom.toLinearMap φ) ((lcoeff S p).restrictScalars R) =
      LinearMap.comp ((lcoeff S' p).restrictScalars R) (mapAlgHom φ).toLinearMap := by
  ext f
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, lcoeff_apply,
    AlgHom.toLinearMap_apply, coeff_mapAlgHom_apply]

lemma mapAlgHom_monomial (φ : S →ₐ[R] S') (n : ℕ) (a : S) :
    (mapAlgHom φ) ((Polynomial.monomial n) a) = (Polynomial.monomial n) (φ a) := by
  simp only [mapAlgHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_mk, coe_mapRingHom, map_monomial,
    RingHom.coe_coe]
-/

open LinearMap TensorProduct in
lemma X_pow_mul_rTensor_monomial {S : Type*} [CommSemiring S] [Algebra R S] {N : Type*}
    [AddCommMonoid N] [Module R N] (k : ℕ) (sn : S ⊗[R] N) :
      X (R := S) ^ k • (LinearMap.rTensor N ((monomial 0).restrictScalars R)) sn =
        (LinearMap.rTensor N ((monomial k).restrictScalars R)) sn := by
    induction sn using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul s n =>
      simp only [rTensor_tmul, coe_restrictScalars, monomial_zero_left]
      rw [smul_tmul', smul_eq_mul, mul_comm, C_mul_X_pow_eq_monomial]

end Polynomial
