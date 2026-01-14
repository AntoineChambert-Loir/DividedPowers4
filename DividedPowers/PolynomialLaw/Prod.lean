/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod
import DividedPowers.PolynomialLaw.Linear

/-! # Linear polynomial laws from/to products

We provide API for the polynomial laws induced by the linear maps `LinearMap.fst`, `LinearMap.snd`,
`LinearMap.inl`, and `LinearMap.inr`.

-/
noncomputable section

open LinearMap MvPolynomial TensorProduct

universe u

variable (R : Type u) [CommSemiring R] (M M' : Type*) [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] {N : Type*} [AddCommMonoid N] [Module R N]
  (f : M →ₚₗ[R] N) (n p : ℕ)

namespace PolynomialLaw

section Prod

lemma fst_ground_apply (m : M × M') : (fst R M M').toPolynomialLaw m = m.1 := by
    simp [toPolynomialLaw_ground_apply, fst_apply]

lemma fst_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : S ⊗[R] (M × M')} :
    (fst R M M').toPolynomialLaw.toFun' S m = ((TensorProduct.prodRight R R S M  M') m).fst := by
  simp only [toPolynomialLaw_toFun']
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

lemma fst_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : S ⊗[R] (M × M')} :
    (fst R M M').toPolynomialLaw.toFun S m = ((TensorProduct.prodRight R R S M  M') m).fst := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (fst R M M').toPolynomialLaw.isCompat_apply, ← toFun'_eq_toFun]
  simp only [fst_toFun'_apply, prodRight_rTensor_fst_eq_rTensor_prodRight]

lemma snd_ground_apply (m : M × M') : (snd R M M').toPolynomialLaw m = m.2 := by
  simp [toPolynomialLaw_ground_apply, snd_apply]

lemma snd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : S ⊗[R] (M × M')} :
    (snd R M M').toPolynomialLaw.toFun' S m = ((TensorProduct.prodRight R R S M  M') m).snd := by
  simp only [toPolynomialLaw_toFun']
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

lemma snd_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : S ⊗[R] (M × M')} :
    (snd R M M').toPolynomialLaw.toFun S m = ((TensorProduct.prodRight R R S M  M') m).snd := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (snd R M M').toPolynomialLaw.isCompat_apply, ← toFun'_eq_toFun]
  simp only [snd_toFun'_apply, prodRight_rTensor_snd_eq_rTensor_prodRight]

lemma sum_fst_snd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : S ⊗[R] (M × M)} :
    (fst R M M + snd R M M).toPolynomialLaw.toFun' S m =
    ((TensorProduct.prodRight R R S M M) m).fst + ((TensorProduct.prodRight R R S M M) m).snd := by
  simp [← fst_toFun'_apply, ← snd_toFun'_apply]

lemma inl_ground_apply (m : M) : (inl R M M').toPolynomialLaw m = (m, 0) := by
  simp [toPolynomialLaw_ground_apply, inl_apply]

lemma inl_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : S ⊗[R] M} :
    (inl R M M').toPolynomialLaw.toFun' S m = ((TensorProduct.inlRight R R S M M') m) := by
  simp only [toPolynomialLaw_toFun', inlRight, coe_comp, LinearEquiv.coe_coe, coe_inl,
    Function.comp_apply]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have h0 : (0 : S ⊗[R] M') = s ⊗ₜ 0 := by simp
    rw [h0, prodRight_symm_tmul]
    simp
  | add m m' hm hm' => simp only [map_add, hm, hm', ← Prod.mk_zero_add_mk_zero]

lemma inl_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : S ⊗[R] M} :
    (inl R M M').toPolynomialLaw.toFun S m = ((TensorProduct.inlRight R R S M M') m) := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (inl R M M').toPolynomialLaw.isCompat_apply, ← toFun'_eq_toFun]
  simp only [inl_toFun'_apply, rTensor_inlRight_eq_inlRight_rTensor]

lemma inr_ground_apply (m : M') : (inr R M M').toPolynomialLaw m = (0, m) := by
  simp [toPolynomialLaw_ground_apply, inr_apply]

lemma inr_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : S ⊗[R] M'} :
    (inr R M M').toPolynomialLaw.toFun' S m = ((TensorProduct.inrRight R R S M M') m) := by
  simp only [toPolynomialLaw_toFun', inrRight, coe_comp, LinearEquiv.coe_coe, coe_inr,
    Function.comp_apply]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have h0 : (0 : S ⊗[R] M) = s ⊗ₜ 0 := by simp
    rw [h0, prodRight_symm_tmul]
    simp
  | add m m' hm hm' =>
    simp only [map_add, hm,  hm', ← Prod.zero_mk_add_zero_mk]

lemma inr_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : S ⊗[R] M'} :
    (inr R M M').toPolynomialLaw.toFun S m = ((TensorProduct.inrRight R R S M M') m) := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (inr R M M').toPolynomialLaw.isCompat_apply, ← toFun'_eq_toFun]
  simp only [inr_toFun'_apply, rTensor_inrRight_eq_inrRight_rTensor]

end Prod
