/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import DividedPowers.ForMathlib.Algebra.Module.LinearMap.Defs
import DividedPowers.ForMathlib.RingTheory.TensorProduct.LinearEquiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Tensor products of a polynomial ring

Adaptations of `TensorProduct.finsuppLeft` when the `Finsupp` is a `Polynomial`.

* `Polynomial.toFinsuppLinearEquiv`, the equivalent of the polynomial ring
  with a Finsupp type, as a linear equivalence.
* `Polynomial.rTensor`, the linear map
  from the tensor product of a polynomial ring to a Finsupp type.
* `Polynomial.mapAlgHom`, `Polynomial.mapAlgEquiv`, the alg hom and the alg equiv
  between polynomial rings induced by an alg hom on coefficients.
* `Polynomial.rTensorAlgHom`, the alg hom morphism from the tensor product of
    a polynomial ring to an algebra to a polynomial ring.
* `Polynomial.rTensorLinearEquiv`, the corresponding linear equiv.
* `Polynomial.rTensorAlgEquiv`, `Polynomial.scalarRTensorAlgEquiv`, the corresponding alg equiv.

## TODO

This will become obsolete when `MonoidAlgebra` is aligned with `Polynomial`, but it is unclear
when such a refactor will take place in Mathlib.

-/

open Polynomial TensorProduct LinearMap LinearEquiv
namespace Polynomial

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

section Module

variable [AddCommMonoid N] [Module R N] (P : Type*) [AddCommMonoid P] [Module R P]
  (S : Type*) [CommSemiring S] [Algebra R S]

/-- The equivalence of the polynomial ring with a Finsupp type, as a linear equivalence -/
def toFinsuppLinearEquiv : S[X] ≃ₗ[S] (ℕ →₀ S) := {
  toFinsuppIso S with
  map_smul' r p := by simp }

variable {S}

theorem toFinsuppLinearEquiv_apply (p : S[X]) :
    toFinsuppLinearEquiv S p = toFinsuppIso S p := rfl

variable (R N) in
/-- The linear map from the tensor product of a polynomial ring to a Finsupp type -/
noncomputable def scalarRTensor : R[X] ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  ((toFinsuppLinearEquiv R).rTensor N).trans (finsuppScalarLeft _ _ _)

lemma scalarRTensor_apply_tmul_apply (p : R[X]) (n : N) (i : ℕ) :
    scalarRTensor R N (p ⊗ₜ[R] n) i = (coeff p i) • n := by
  simp [scalarRTensor, toFinsuppLinearEquiv_apply, coeff]

lemma scalarRTensor_apply_tmul (p : R[X]) (n : N) :
    scalarRTensor R N (p ⊗ₜ[R] n) = p.sum (fun i r => Finsupp.single i (r • n)) := by
  ext i
  rw [scalarRTensor_apply_tmul_apply, sum_def, Finset.sum_apply', Finset.sum_eq_single i
    (fun _ _ h => Finsupp.single_eq_of_ne h.symm) ?_ , Finsupp.single_eq_same]
  intro h
  simp only [mem_support_iff, ne_eq, not_not] at h
  rw [h, zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]

lemma scalarRTensor_apply (pn : R[X] ⊗[R] N) (d : ℕ) :
    scalarRTensor R N pn d = TensorProduct.lid R N ((lcoeff R d).rTensor N pn) := by
  rw [← LinearEquiv.symm_apply_eq, lid_symm_apply]
  induction pn using TensorProduct.induction_on with
  | zero => simp
  | tmul p n => simp [scalarRTensor_apply_tmul_apply, TensorProduct.smul_tmul']
  | add x y hx hy => simp [tmul_add, hx, hy]

variable (R S N) in
/-- The linear map from the tensor product of a polynomial ring to a Finsupp type. -/
noncomputable def rTensor : S[X] ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  ((toFinsuppLinearEquiv S).rTensor' N).trans (TensorProduct.finsuppLeft' _ _ _ _ S)

lemma rTensor_apply_tmul_apply (p : Polynomial S) (n : N) (i : ℕ) :
    rTensor R N S (p ⊗ₜ[R] n) i = (coeff p i) ⊗ₜ[R] n := by
  simp [rTensor, LinearEquiv.trans_apply, finsuppLeft'_apply, LinearEquiv.rTensor'_apply,
    toFinsuppLinearEquiv_apply, finsuppLeft_apply_tmul_apply, coeff]

lemma rTensor_apply_tmul (p : Polynomial S) (n : N) :
    rTensor R N S (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp [rTensor, LinearEquiv.trans_apply, finsuppLeft'_apply, LinearEquiv.rTensor'_apply,
    finsuppLeft_apply_tmul]
  simp [toFinsuppLinearEquiv_apply, Polynomial.sum_def, Finsupp.sum, Polynomial.support_toFinsupp,
    Polynomial.coeff]

lemma rTensor_apply (t : Polynomial S ⊗[R] N) (d : ℕ) :
    rTensor R N S t d = ((lcoeff S d).restrictScalars R).rTensor N t := by
  simp [rTensor, LinearEquiv.trans_apply, finsuppLeft'_apply,
    LinearEquiv.rTensor'_apply, LinearEquiv.rTensor, TensorProduct.congr, finsuppLeft_apply,
    LinearMap.rTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  rfl

end Module

section Algebra

variable (R N) [CommSemiring N] [Algebra R N] (S : Type*) [CommSemiring S] [Algebra R S]

/-- The alg hom morphism from the tensor product of a polynomial ring to
  an algebra to a polynomial ring. -/
noncomputable def rTensorAlgHom :
    (Polynomial S) ⊗[R] N →ₐ[S] Polynomial (S ⊗[R] N) :=
  Algebra.TensorProduct.lift
    (mapAlgHom Algebra.TensorProduct.includeLeft)
    ((IsScalarTower.toAlgHom R (S ⊗[R] N) _).comp Algebra.TensorProduct.includeRight)
    (fun p n => by simp only [commute_iff_eq, mul_comm])

variable {R N S}

lemma rTensorAlgHom_coeff_apply_tmul (p : Polynomial S) (n : N) (d : ℕ) :
    coeff (rTensorAlgHom R N S (p ⊗ₜ[R] n)) d = (coeff p d) ⊗ₜ[R] n := by
  rw [rTensorAlgHom, Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, ← C_eq_algebraMap, mul_comm, coeff_C_mul]
  simp [mapAlgHom, coeff_map]

variable (R S N)
/-- The linear equiv from the tensor product of a polynomial ring by an algebra
  to a polynomial ring. -/
noncomputable def rTensorLinearEquiv : S[X] ⊗[R] N ≃ₗ[S] (S ⊗[R] N)[X] :=
  (LinearEquiv.rTensor' N (toFinsuppLinearEquiv S)).trans
    ((finsuppLeft' _ _ _ _ S).trans ((toFinsuppLinearEquiv _).symm.restrictScalars _))

variable {R N S} (p : Polynomial S) (n : N) (e : ℕ)

lemma rTensorLinearEquiv_tmul_toFinsupp :
    (rTensorLinearEquiv R N S (p ⊗ₜ[R] n)).toFinsupp =
      TensorProduct.finsuppLeft' _ _ _ _ S (p.toFinsupp ⊗ₜ[R] n) := by rfl

lemma rTensorLinearEquiv_coeff_tmul  :
    coeff (rTensorLinearEquiv R N S (p ⊗ₜ[R] n)) e = (coeff p e) ⊗ₜ[R] n := by
  dsimp only [coeff, AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe]
  rw [rTensorLinearEquiv_tmul_toFinsupp, finsuppLeft'_apply, finsuppLeft_apply_tmul_apply]

lemma rTensorAlgHom_toLinearMap :
    (rTensorAlgHom R N S).toLinearMap = (rTensorLinearEquiv _ _ _).toLinearMap:= by
  ext d n e
  dsimp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, coe_comp, Function.comp_apply,
    AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
  rw [rTensorAlgHom_coeff_apply_tmul, rTensorLinearEquiv_coeff_tmul]

lemma rTensorAlgHom_apply_eq (p : Polynomial S ⊗[R] N) :
    rTensorAlgHom R N S p = rTensorLinearEquiv R N S p := by
  rw [← AlgHom.toLinearMap_apply, rTensorAlgHom_toLinearMap, LinearEquiv.coe_coe]

variable (R N S)

/-- The alg equiv from the tensor product of a polynomial ring and an algebra
  to a polynomial ring -/
noncomputable def rTensorAlgEquiv :
    (Polynomial S) ⊗[R] N ≃ₐ[S] Polynomial (S ⊗[R] N) := by
  apply AlgEquiv.ofLinearEquiv (rTensorLinearEquiv R N S)
  · ext e
    simp only [Algebra.TensorProduct.one_def, rTensorLinearEquiv_coeff_tmul, coeff_one]
    split_ifs <;> simp
  · intro x y
    rw [← rTensorAlgHom_apply_eq (S := S)]
    simp [_root_.map_mul, rTensorAlgHom_apply_eq]

/-- The tensor product of a polynomial ring  with an algebra is a polynomial ring -/
noncomputable def scalarRTensorAlgEquiv : R[X] ⊗[R] N ≃ₐ[R] Polynomial N :=
  (rTensorAlgEquiv R N R).trans (mapAlgEquiv (Algebra.TensorProduct.lid R N))

end Algebra

theorem rTensor_sum {S : Type*} [CommSemiring S] [Algebra R S] (φ : ℕ → S) (sXn : S[X] ⊗[R] M) :
    (rTensor R M S sXn).sum (fun p sn ↦ (φ p) • sn) =
      (Polynomial.lsum (fun n ↦ (LinearMap.lsmul S S (φ n)).restrictScalars R)).rTensor M sXn := by
  induction sXn using TensorProduct.induction_on with
  | zero => simp
  | tmul p n =>
    induction p using Polynomial.induction_on with
    | C s =>
      rw [Finsupp.sum_eq_single 0 ?_ (fun _ => by rw [smul_zero]),
      rTensor_apply, LinearMap.rTensor_tmul,  LinearMap.rTensor_tmul]
      simp [TensorProduct.smul_tmul']
      · intro b _ hb
        simp only [rTensor_apply,  LinearMap.rTensor_tmul, coe_restrictScalars, lcoeff_apply]
        rw [Polynomial.coeff_C, if_neg hb, zero_tmul, smul_zero]
    | add p q hp hq => rw [add_tmul, LinearEquiv.map_add, Finsupp.sum_add_index
        (fun _ _ ↦ smul_zero _) (fun _ _ ↦ smul_add _ ), hp, hq, LinearMap.map_add]
    | monomial p s _ =>
      rw [Finsupp.sum_eq_single (p + 1) (fun _ _ hb ↦ by simp [rTensor_apply, if_neg hb])
        (fun _ ↦ smul_zero (φ (p + 1))), rTensor_apply, LinearMap.rTensor_tmul]
      simp only [coe_restrictScalars, lcoeff_apply, coeff_C_mul, coeff_X_pow,
          ↓reduceIte, mul_one, LinearMap.rTensor_tmul, Polynomial.lsum_apply,
          lsmul_apply, smul_eq_mul]
      rw [C_mul_X_pow_eq_monomial, sum_monomial_index _ _ (by rw [mul_zero]), smul_tmul',
          smul_eq_mul]
  | add p q hp hq => rw [LinearEquiv.map_add, Finsupp.sum_add_index (fun _ _ ↦ smul_zero _)
      (fun _ _ ↦ smul_add _ ), hp, hq, LinearMap.map_add]

theorem rTensor_sum_id {S : Type*} [CommSemiring S] [Algebra R S] (sm : S[X] ⊗[R] M) :
  (((Polynomial.rTensor R M S) sm).sum fun _ m ↦ m) =
    (LinearMap.rTensor M (AlgHom.restrictScalars R (aeval 1)).toLinearMap) sm := by
  convert rTensor_sum (R := R) (fun _ ↦ 1) sm
  rw [_root_.one_smul]
  ext p
  simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', coe_aeval_eq_eval,
    Polynomial.lsum_apply, coe_restrictScalars, lsmul_apply, smul_eq_mul, one_mul, eval_eq_sum]
  exact congr_arg₂ _ rfl (by simp)

open TensorProduct in
lemma rTensor_monomial_eq {S : Type*} [CommSemiring S] [Algebra R S] {sm : S ⊗[R] M} {p n : ℕ} :
    rTensor R M S ((LinearMap.rTensor M ((monomial p).restrictScalars R)) sm) n =
      if p = n then sm else 0 := by
  simp only [rTensor_apply, ← rTensor_comp_apply]
  have : (lcoeff S n) ∘ₗ (monomial p) = if p = n then LinearMap.id else 0 := by
    ext
    simp only [coe_comp, Function.comp_apply, lcoeff_apply, coeff_monomial]
    split_ifs <;> simp
  simp only [← restrictScalars_comp, this]
  split_ifs <;> simp

end Polynomial
