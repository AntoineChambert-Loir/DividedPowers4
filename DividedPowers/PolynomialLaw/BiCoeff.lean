/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Basic
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod
import DividedPowers.PolynomialLaw.Coeff

/- # Bicoefficients of polynomial laws.

## Main definitions

* `Module.biGenerize`: the `R`-linear map sending  `m : M × M'` to the sum
  `X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)` in `MvPolynomial (Fin 2) R ⊗[R] (M × M')`.

* `Module.biGenerizeBaseChange`: the `S`-linear map that sends `s ⊗ₜ m : S ⊗[R] (M × M')` to
  `s • X 0 ⊗ₜ[R] (m.1, 0) + s •X 1 ⊗ₜ[R] (0, m.2)` in `(MvPolynomial (Fin 2) S) ⊗[R] (M × M')`.

* `PolynomialLaw.biCoeff`: the bicoefficients of a `PolynomialLaw`, as linear maps.

* `PolynomialLaw.biCoeffBaseChange`: the bicoefficients of a polynomial law, after base change,
 as a `Finsupp`.

## Main results

* `PolynomialLaw.toFun_add_tmul_eq_biCoeff_sum`, `PolynomialLaw.toFun_tmul_fst_eq_biCoeff_sum`,
  `PolynomialLaw.toFun_tmul_snd_eq_biCoeff_sum` provide formulas for applications of `f` in terms
  of sums of bicoefficients.

## Notes

See the file `DividedPowerAlgebra.PolynomialLaw.MultiCoeff` for the generalization to
finite product types.

-/

universe u

variable {R : Type u} [CommSemiring R]

namespace Module

variable {N M M' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R M']

open MvPolynomial TensorProduct

section biGenerize

/-- `biGenerize` is the `R`-linear map sending `m : M × M'` to the sum
  `X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2) : MvPolynomial (Fin 2) R ⊗[R] (M × M')`. -/
noncomputable def biGenerize :
    (M × M') →ₗ[R] MvPolynomial (Fin 2) R ⊗[R] (M × M') where
  toFun m       := X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)
  map_add' p q  := by
    simp only [Prod.fst_add, Prod.snd_add, ← Prod.mk_zero_add_mk_zero, ← Prod.zero_mk_add_zero_mk,
      tmul_add]
    abel
  map_smul' r p := by simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add,
    ← Prod.smul_mk_zero, ← Prod.smul_zero_mk, tmul_smul]

theorem biGenerize_eq_generize (m : M × M') :
    (biGenerize m) = (generize (R := R) (![(m.1, 0), (0, m.2)])) := by
  simp [generize, biGenerize]

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- `biGenerizeBaseChange` is the `S`-linear map that sends `s ⊗ₜ m : S ⊗[R] (M × M')` to
  `s • X 0 ⊗ₜ[R] (m.1, 0) + s •X 1 ⊗ₜ[R] (0, m.2)` in `(MvPolynomial (Fin 2) S) ⊗[R] (M × M')`. -/
noncomputable def biGenerizeBaseChange :
    (S ⊗[R] (M × M')) →ₗ[S] (MvPolynomial (Fin 2) S) ⊗[R] (M × M') where
  toFun sm := LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv
    ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
      ((X 0) ⊗ₜ (compFstRight R S S M M' sm) + (X 1) ⊗ₜ (compSndRight R S S M M' sm)))
  map_add' x y := by
    simp only [← map_add]
    rw [add_add_add_comm]
    simp only [Fin.isValue, map_add, tmul_add]
  map_smul' s x := by
    simp only [Fin.isValue, map_smul, map_add, RingHom.id_apply, smul_add]
    congr
    all_goals
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r m =>
        simp [compFstRight_tmul, inlRight_tmul, compSndRight_tmul, inrRight_tmul,
        smul_tmul', scalarRTensorAlgEquiv, rTensorAlgHom,
          smul_eq_C_mul _ s, mul_left_comm (C s)]
      | add x y hx hy => simp only [Fin.isValue, map_add, smul_add, tmul_add, ← hx, ← hy]

lemma biGenerizeBaseChange_apply_tmul (s : S) (m : M × M') :
    biGenerizeBaseChange (s ⊗ₜ[R] m) = s • X 0 ⊗ₜ[R] (m.1, 0) + s •X 1 ⊗ₜ[R] (0, m.2) := by
  simp [biGenerizeBaseChange, map_add, scalarRTensorAlgEquiv, smul_tmul', compFstRight_tmul,
    inlRight_tmul, rTensorAlgHom, mul_comm _ (C s), C_mul', compSndRight_tmul, inrRight_tmul]

lemma biGenerizeBaseChange_apply_eq (sm : S ⊗[R] (M × M')) :
    biGenerizeBaseChange sm = (LinearEquiv.rTensor (R := R) (M × M')
      scalarRTensorAlgEquiv.toLinearEquiv
        ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
          ((X 0) ⊗ₜ (compFstRight R S S M M' sm) + (X 1) ⊗ₜ (compSndRight R S S M M' sm)))) := by
  simp only [biGenerizeBaseChange, Fin.isValue, map_add, LinearMap.coe_mk, AddHom.coe_mk]

end biGenerize

end Module

/- # Polynomial laws. -/

namespace PolynomialLaw

open Finset LinearMap MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {N M M' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R M']

section biCoeff

variable (m : M × M') (f : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ)

/-- Given `m : M × M'`, `biGenerize' m` is the `R`-linear map sending
`f : (M × M') →ₚₗ[R] N` to the term of `MvPolynomial (Fin 2) R ⊗[R] N` obtained by applying
`f.toFun (MvPolynomial (Fin 2) R)` to the sum `X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)`.
This is provided as an auxiliary map for the definition `PolynomialLaw.biCoeff`. -/
noncomputable def biGenerize' :
    ((M × M') →ₚₗ[R] N) →ₗ[R] MvPolynomial (Fin 2) R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial (Fin 2) R) (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

private noncomputable def biCoeff_aux : N :=
  scalarRTensor.toLinearMap.comp (biGenerize' m) f ((finTwoArrowEquiv' ℕ).symm n)

private lemma biCoeff_aux_apply :
  biCoeff_aux m f n = scalarRTensor.toLinearMap.comp (biGenerize' m) f
      ((finTwoArrowEquiv' ℕ).symm n) := rfl

private lemma finite_support_biCoeff_aux :
    (Function.support (biCoeff_aux m f)).Finite := by
  apply Set.Finite.of_injOn (f := (finTwoArrowEquiv' ℕ).symm) ?_
    (Equiv.injective (finTwoArrowEquiv' ℕ).symm).injOn (Finsupp.finite_support
    (scalarRTensor.toLinearMap.comp (biGenerize' m) f))
  simp only [Set.MapsTo, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Function.mem_support,
    ne_eq, Finsupp.fun_support_eq, mem_coe, Finsupp.mem_support_iff, Prod.forall]
  exact fun _ _ hab ↦ by simpa using hab

/-- The bicoefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def biCoeff : ((M × M') →ₚₗ[R] N) →ₗ[R] (ℕ × ℕ) →₀ N where
  toFun g := Finsupp.ofSupportFinite (fun n ↦ scalarRTensor.toLinearMap.comp (biGenerize' m) g
      ((finTwoArrowEquiv' ℕ).symm n)) (finite_support_biCoeff_aux m g)
  map_add' mn mn' := by simp [Finsupp.ext_iff, Finsupp.ofSupportFinite_coe]
  map_smul' r nm := by simp [Finsupp.ext_iff, Finsupp.ofSupportFinite_coe]

open Module

private theorem coeff_support_finite : (Function.support fun n ↦
    ((coeff ![(m.1, 0), (0, m.2)]) f) ((finTwoArrowEquiv' ℕ).symm n)).Finite :=
  Set.Finite.of_injOn (f := (finTwoArrowEquiv' ℕ).symm) (by simp [Set.MapsTo]) (Equiv.injective
    (finTwoArrowEquiv' ℕ).symm).injOn (Finsupp.finite_support (coeff ![(m.1, 0), (0, m.2)] f))

theorem biCoeff_eq_coeff : biCoeff m f = Finsupp.ofSupportFinite
    (fun n ↦ coeff ![(m.1, 0), (0, m.2)] f ((finTwoArrowEquiv' ℕ).symm n))
      (coeff_support_finite m f) := by
  simp [biCoeff, biGenerize', coeff, generize', generize, coe_mk, AddHom.coe_mk]

theorem biCoeff_apply_eq_coeff_apply :
    biCoeff m f n = coeff ![(m.1, 0), (0, m.2)] f ((finTwoArrowEquiv' ℕ).symm n) := by
  simp [biCoeff_eq_coeff, Finsupp.ofSupportFinite_coe]

theorem toFun_biGenerize_eq : f.toFun (MvPolynomial (Fin 2) R) (biGenerize m) =
    (biCoeff m f).sum (fun k n ↦ (monomial ((finTwoArrowEquiv' ℕ).symm k) 1) ⊗ₜ n) := by
  simp only [biGenerize_eq_generize, Nat.succ_eq_add_one, Nat.reduceAdd, toFun_generize_eq,
    finTwoArrowEquiv'_symm_apply]
  simp only [Finsupp.sum, biCoeff_apply_eq_coeff_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    finTwoArrowEquiv'_symm_apply]
  apply Finset.sum_bij (fun n _ ↦ finTwoArrowEquiv' ℕ n) _ _ _
    (fun _ _ ↦ by simp [Finsupp.ofSupportFinite_fin_two_eq])
  · intro _ hn
    simpa [biCoeff_apply_eq_coeff_apply, Finsupp.ofSupportFinite_fin_two_eq] using hn
  · intro _ _ _ _ h
    simpa [Finsupp.ext_iff, Fin.forall_fin_two] using h
  · intro n hn
    exact ⟨(finTwoArrowEquiv' ℕ).symm n, by simpa [biCoeff_eq_coeff] using hn,
      by simp only [Equiv.apply_symm_apply]⟩

lemma biCoeff_apply (g : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ) :
    biCoeff m g n =
      scalarRTensor.toLinearMap.comp (biGenerize' m) g ((finTwoArrowEquiv' ℕ).symm n) := rfl

theorem biCoeff_eq :
  biCoeff m f n = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R
    ((finTwoArrowEquiv' ℕ).symm n)))
      (f.toFun (MvPolynomial (Fin 2) R) (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)))) := by
  simp only [biCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_mk, AddHom.coe_mk,
    Fin.isValue]
  exact scalarRTensor_apply _ _

/-- A formula for `f.toFun S (r ⊗ₜ[R] (m.1, 0) + s ⊗ₜ (0, m.2))` as a sum of bicoefficients. -/
theorem toFun_add_tmul_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r s : S) :
    f.toFun S (r ⊗ₜ[R] (m.1, 0) + s ⊗ₜ (0, m.2)) =
      (biCoeff m f).sum (fun k n ↦ (r ^ k.1 * s ^ k.2) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval ((finTwoArrowEquiv' S).symm (r, s))))
     (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2))
  simp only [Fin.isValue, Function.comp_apply, map_add, rTensor_tmul, AlgHom.toLinearMap_apply,
    aeval_X] at this
  simp only [finTwoArrowEquiv', Fin.isValue, Equiv.coe_fn_symm_mk, Finsupp.ofSupportFinite_coe,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  let h := toFun_biGenerize_eq m f
  simp only [biGenerize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul, finTwoArrowEquiv',
    Finsupp.ofSupportFinite_coe ]

/-- A formula for `f.toFun S (r ⊗ₜ[R] (m.1, 0))` as a sum of bicoefficients. -/
theorem toFun_tmul_fst_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) :
    f.toFun S (r ⊗ₜ[R] (m.1, 0)) =
      ((biCoeff (m.1, 0) f).sum fun k n ↦ (r ^ k.1 * r ^ k.2) ⊗ₜ[R] n) := by
  have : r ⊗ₜ[R] (m.1, (0 : M')) = (r, r).1 ⊗ₜ[R] (m.1, 0) + (r, r).2 ⊗ₜ[R] (0, 0) := by
    simp [Prod.mk_zero_zero, tmul_zero, add_zero]
  rw [this, toFun_add_tmul_eq_biCoeff_sum (m.1, 0)]

/-- A formula for `f.toFun S (r ⊗ₜ[R] (0, m.2))` as a sum of bicoefficients. -/
theorem toFun_tmul_snd_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) :
    f.toFun S (r ⊗ₜ[R] (0, m.2)) =
      ((biCoeff (0, m.2) f).sum fun k n ↦ (r ^ k.1 * r ^ k.2) ⊗ₜ[R] n) := by
  have : r ⊗ₜ[R] ((0 : M), m.2) = (r, r).1 ⊗ₜ[R] (0, 0) + (r, r).2 ⊗ₜ[R] (0, m.2) := by
    simp [Prod.mk_zero_zero, tmul_zero, zero_add]
  rw [this, toFun_add_tmul_eq_biCoeff_sum (0, m.2)]

end biCoeff

open Function

variable (r : R × R) (r₁ r₂ : R) (m m₁ m₂ : M × M') (f : (M × M') →ₚₗ[R] N) (k : ℕ × ℕ)

theorem ground_apply_sum_smul_eq_biCoeff_sum :
    ground f (r.1 • (m.1, 0) + r.2 • (0, m.2)) =
      (biCoeff m f).sum (fun k n ↦ (r.1 ^ k.1 * r.2 ^ k.2) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_add, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', toFun_add_tmul_eq_biCoeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ ↦ by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])

theorem ground_apply_smul_eq_biCoeff_sum :
    ground f (r₁ • m₁) = (biCoeff m₁ f).sum (fun k n ↦ r₁ ^ (k.1 + k.2) • n) := by
  suffices r₁ • m₁ = (r₁, r₁).1 • (m₁.1, 0) + (r₁, r₁).2 • (0, m₁.2) by
    rw [this, ground_apply_sum_smul_eq_biCoeff_sum]
    exact sum_congr rfl (by simp [pow_add])
  simp only [← smul_add, Prod.mk_add_mk, add_zero, zero_add]

variable {S : Type*} [CommSemiring S] [Algebra R S] {m}

theorem biCoeff_injective
    (hm : Submodule.span R (Set.range ![(m.1, (0 : M')), ((0 : M), m.2)]) = ⊤) :
    Function.Injective (biCoeff m : ((M × M') →ₚₗ[R] N) →ₗ[R] (ℕ × ℕ) →₀ N) := fun f g h ↦ by
  simp only [biCoeff_eq_coeff, Nat.succ_eq_add_one, Nat.reduceAdd, finTwoArrowEquiv'_symm_apply,
    Finsupp.ext_iff, Finsupp.ofSupportFinite_coe, Prod.forall] at h
  apply coeff_injective hm
  ext n
  simpa [Finsupp.ofSupportFinite_fin_two_eq] using h (n 0) (n 1)

theorem biCoeff_inj (hm : Submodule.span R (Set.range ![(m.1, (0 : M')), ((0 : M), m.2)]) = ⊤)
    {f g : (M × M') →ₚₗ[R] N} :
    (biCoeff m f) = (biCoeff m g ) ↔ f = g := (biCoeff_injective hm).eq_iff

open Module

variable (f : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ) (sm : S ⊗[R] (M × M'))

/-- The bicoefficients of a polynomial law, after base change, as a `Finsupp`. -/
noncomputable def biCoeffBaseChange' : (Fin 2 →₀ ℕ) →₀ S ⊗[R] N :=
  finsuppLeft R S N _ (f.toFun _ (biGenerizeBaseChange sm))

/-- The bicoefficients of a polynomial law, after base change, as a `Finsupp`. -/
noncomputable def biCoeffBaseChange : (ℕ × ℕ) →₀ S ⊗[R] N :=
  Finsupp.ofSupportFinite (fun n ↦ finsuppLeft R S N _ (f.toFun _ (biGenerizeBaseChange sm))
    ((finTwoArrowEquiv' ℕ).symm n)) (Set.Finite.of_injOn (f := (finTwoArrowEquiv' ℕ).symm)
    (by simp [Set.MapsTo]) (Equiv.injective
    (finTwoArrowEquiv' ℕ).symm).injOn (Finsupp.finite_support
    (finsuppLeft R S N _ (f.toFun _ (biGenerizeBaseChange sm)))))

lemma biCoeffBaseChange_eq :
  (biCoeffBaseChange f sm) n = (biCoeffBaseChange' f sm) ((finTwoArrowEquiv' ℕ).symm n) := rfl

theorem biGenerize_eq_sum_biCoeffBaseChange' :
    f.toFun _ (biGenerizeBaseChange sm) = (f.biCoeffBaseChange' sm).sum
      (fun k ↦ AlgebraTensorModule.map (monomial k) LinearMap.id) := by
  simp only [biCoeffBaseChange']
  set sn := finsuppLeft R S N _ (f.toFun _ (biGenerizeBaseChange sm)) with hsn
  rw [← LinearEquiv.symm_apply_eq] at hsn
  rw [← hsn, finsuppLeft_symm_apply_eq_sum]

theorem biGenerize_eq_sum_biCoeffBaseChange :
    f.toFun _ (biGenerizeBaseChange sm) = (f.biCoeffBaseChange sm).sum
      (fun k ↦ AlgebraTensorModule.map (monomial ((finTwoArrowEquiv' ℕ).symm k)) LinearMap.id) := by
  rw [biGenerize_eq_sum_biCoeffBaseChange']
  apply Finset.sum_bij (fun n _ ↦ finTwoArrowEquiv' ℕ n) _ _ _ _
  · intro a ha
    simpa [biCoeffBaseChange, biCoeffBaseChange', Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_fin_two_eq] using ha
  · intro _ _ _ _ h
    simpa [Finsupp.ext_iff, Fin.forall_fin_two] using h
  · intro n hn
    refine ⟨(finTwoArrowEquiv' ℕ).symm n, ?_,
      by simp only [Equiv.apply_symm_apply]⟩
    simpa [biCoeffBaseChange, biCoeffBaseChange', Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_fin_two_eq] using hn
  · intro n hn
    simp [Finsupp.ofSupportFinite_fin_two_eq, biCoeffBaseChange, biCoeffBaseChange',
      Finsupp.ofSupportFinite_coe]

lemma biCoeffBaseChange'_apply' :
  biCoeffBaseChange' f sm = MvPolynomial.rTensor
    (f.toFun (MvPolynomial (Fin 2) S) (biGenerizeBaseChange sm)) := by
ext k
simp only [biCoeffBaseChange']
rw [biGenerize_eq_sum_biCoeffBaseChange]
rfl

lemma biCoeffBaseChange_apply' :
  biCoeffBaseChange f sm n = MvPolynomial.rTensor
    (f.toFun (MvPolynomial (Fin 2) S) (biGenerizeBaseChange sm))
      ((finTwoArrowEquiv' ℕ).symm n) := by
rw [← biCoeffBaseChange'_apply', biCoeffBaseChange_eq]

lemma biCoeffBaseChange'_apply :
    biCoeffBaseChange' f sm = MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
      (LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv
        ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
          (X 0 ⊗ₜ[R] (compFstRight R S S M M') sm + X 1 ⊗ₜ[R] (compSndRight R S S M M') sm)))) := by
  rw [biCoeffBaseChange'_apply', biGenerizeBaseChange_apply_eq]

lemma biCoeffBaseChange_apply :
    biCoeffBaseChange f sm = fun n ↦ MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
      (LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv
        ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
          (X 0 ⊗ₜ[R] (compFstRight R S S M M') sm + X 1 ⊗ₜ[R] (compSndRight R S S M M') sm))))
          ((finTwoArrowEquiv' ℕ).symm n) := by
  ext n
  rw [biCoeffBaseChange_eq, biCoeffBaseChange'_apply]

variable (m)

lemma biCoeffBaseChange'_apply_tmul (k' : Fin 2 →₀ ℕ) (s : S) :
   biCoeffBaseChange' f (s ⊗ₜ m) k' = MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
      (LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
      (X 0 ⊗ₜ[R] (s ⊗ₜ (m.1, 0)) + X 1 ⊗ₜ[R] (s ⊗ₜ (0, m.2))))))
        k' := by
  rw [biCoeffBaseChange'_apply]
  have h : ((0 : S ⊗ M), s ⊗ₜ[R] m.2) = (s ⊗ₜ[R] 0, s ⊗ₜ[R] m.2) := by rw [tmul_zero]
  have h' : (s ⊗ₜ[R] m.1, (0 : S ⊗ M')) = (s ⊗ₜ[R] m.1, s ⊗ₜ[R] 0) := by rw [tmul_zero]
  simp [TensorProduct.compFstRight, inlRight, fstRight, TensorProduct.compSndRight,
    inrRight, sndRight, h, h', prodRight_symm_tmul]

lemma biCoeffBaseChange_apply_tmul (s : S) :
   biCoeffBaseChange f (s ⊗ₜ m) k = MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
      (LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
      (X 0 ⊗ₜ[R] (s ⊗ₜ (m.1, 0)) + X 1 ⊗ₜ[R] (s ⊗ₜ (0, m.2))))))
        ((finTwoArrowEquiv' ℕ).symm k) := by
  rw [biCoeffBaseChange_eq, biCoeffBaseChange'_apply_tmul]

variable (s : S × S) (m : M × M')

lemma biCoeffBaseChange_apply_smul [Nontrivial R] :
    biCoeffBaseChange f (s.1 • TensorProduct.compFstRight R S S M M' sm +
      s.2 • TensorProduct.compSndRight R S S M M' sm) n  =
      (s.1 ^ n.1 * s.2 ^ n.2) • biCoeffBaseChange f sm n := by
  let g : Fin 2 → MvPolynomial (Fin 2) S := ![(C s.1) * X (0 : Fin 2), (C s.2) * X 1]
  let ψ : MvPolynomial (Fin 2) S →ₐ[R] MvPolynomial (Fin 2) S :=
    (aeval (R := S) ![(C s.1) * X (0 : Fin 2), (C s.2) * X 1]).restrictScalars R
  suffices ((LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
        (X 0 ⊗ₜ[R] compFstRight R S S M M' (s.1 • (compFstRight R S S M M' sm) +
          s.2 • (compSndRight R S S M M' sm)) +
          X 1 ⊗ₜ[R] compSndRight R S S M M' (s.1 • (compFstRight R S S M M' sm) +
            s.2 • (compSndRight R S S M M' sm))))) =
      ((LinearMap.rTensor (M × M') ψ.toLinearMap)
        ((LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
            (X 0 ⊗ₜ[R] (compFstRight R S S M M' sm) + X 1 ⊗ₜ (compSndRight R S S M M' sm))))) by
    simp only [biCoeffBaseChange_apply, this, ← f.isCompat_apply]
    clear this
    generalize ht : (f.toFun (MvPolynomial (Fin 2) S)
          ((LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
              ((X 0 : MvPolynomial (Fin 2) R) ⊗ₜ[R] (compFstRight R S S M M' sm) +
        (X 1 : MvPolynomial (Fin 2) R) ⊗ₜ (compSndRight R S S M M' sm))))) = t
    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (s.1 ^ n.1 * s.2 ^ n.2)).mk'_apply,
        ← coe_restrictScalars R, ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    rw [eq_comm]
    dsimp only [LinearMap.rTensor, TensorProduct.map]
    apply lift.unique
    intro f k
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, lift.tmul,
      lcoeff_apply, mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply, smul_tmul']
    apply congr_arg₂ _ _ rfl
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | monomial k' a =>
        simp only [ψ, coeff_monomial]
        split_ifs with h <;>
        rw [finTwoArrowEquiv'_symm_apply] at h
        · rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial,
           algebraMap_eq, coeff_C_mul, Finsupp.prod_pow]
          simp only [finTwoArrowEquiv'_symm_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
            Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [mul_pow, mul_pow, mul_mul_mul_comm, ← C_pow, ← C_pow, ← map_mul, coeff_C_mul,
            X_pow_mul_X_pow_eq_prod', prod_X_pow_eq_monomial', coeff_monomial, if_pos rfl]
          simp; rfl
        · simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, algebraMap_eq]
          rw [coeff_C_mul, Finsupp.prod_pow]
          simp only [finTwoArrowEquiv'_symm_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
            Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [mul_pow, mul_pow, mul_mul_mul_comm, ← C_pow, ← C_pow, ← map_mul, coeff_C_mul,
            X_pow_mul_X_pow_eq_prod', prod_X_pow_eq_monomial', coeff_monomial, if_neg h]
          simp
  simp only [map_add]
  congr
  · simp only [Fin.isValue, map_smul, LinearEquiv.rTensor_apply,
      AlgEquiv.toLinearEquiv_toLinearMap, ← rTensor_comp_apply]
    induction sm using TensorProduct.induction_on with
    | zero => simp [map_zero, smul_zero, tmul_zero]
    | tmul t m =>
      simp only [compFstRight_tmul, compSndRight_tmul,
        smul_tmul', compFstRight_inrRight_eq, inlRight_tmul]
      simp only [Fin.isValue, smul_eq_mul, smul_zero, add_zero, assoc_symm_tmul, rTensor_tmul,
        AlgEquiv.toLinearMap_apply, coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
      simp only [scalarRTensorAlgEquiv, Fin.isValue, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
        mapAlgEquiv_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
        AlgHom.coe_restrictScalars', ψ]
      congr
      simp only [Fin.isValue, rTensorAlgHom_apply_eq, rTensor_apply_tmul, Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have : Finsupp.support (X (R := R) (0 : Fin 2)) = MvPolynomial.support (X 0) := rfl
      simp only [this, support_X, Finset.mem_singleton] at hd
      simp only [hd, MvPolynomial.aeval_def, algebraMap_eq, eval₂_map]
      simp only [eval₂, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Finsupp.prod_pow,
        map_zero, zero_mul, Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul, X,
        ← single_eq_monomial, Finsupp.single_eq_same, _root_.one_smul]
      rw [Finset.prod_eq_single 0 (fun _ _ hj ↦ by
        rw [Finsupp.single_eq_of_ne hj, pow_zero]) (fun hj ↦ absurd (Finset.mem_univ _) hj)]
      simp [single_eq_monomial, mul_comm s.1 t, C_mul_monomial]
    | add sm sm' h h' =>
      simp only [map_add, smul_add, tmul_add] at h h' ⊢
      rw [← h, ← h']
      abel
  · simp only [Fin.isValue, map_smul, LinearEquiv.rTensor_apply,
      AlgEquiv.toLinearEquiv_toLinearMap, ← rTensor_comp_apply]
    induction sm using TensorProduct.induction_on with
    | zero => simp [map_zero, smul_zero, tmul_zero]
    | tmul t m =>
      simp only [compFstRight_tmul, compSndRight_tmul,
        smul_tmul', compSndRight_inlRight_eq, inrRight_tmul]
      simp only [Fin.isValue, smul_eq_mul, smul_zero, zero_add, assoc_symm_tmul, rTensor_tmul,
        AlgEquiv.toLinearMap_apply, coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
      simp only [scalarRTensorAlgEquiv, Fin.isValue, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
        mapAlgEquiv_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
        AlgHom.coe_restrictScalars', ψ]
      congr
      simp only [Fin.isValue, rTensorAlgHom_apply_eq, rTensor_apply_tmul, Finsupp.sum, map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have : Finsupp.support (X (R := R) (1 : Fin 2)) = MvPolynomial.support (X 1) := rfl
      simp only [this, support_X, Finset.mem_singleton] at hd
      simp only [hd, MvPolynomial.aeval_def, algebraMap_eq, eval₂_map]
      simp only [eval₂, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Finsupp.prod_pow,
        map_zero, zero_mul, Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul, X,
        ← single_eq_monomial, Finsupp.single_eq_same, _root_.one_smul]
      rw [Finset.prod_eq_single 1 (fun _ _ hj ↦ by
        rw [Finsupp.single_eq_of_ne hj, pow_zero]) (fun hj ↦ absurd (Finset.mem_univ _) hj)]
      simp [single_eq_monomial, mul_comm s.2 t, C_mul_monomial]
    | add sm sm' h h' =>
      simp only [map_add, smul_add, tmul_add] at h h' ⊢
      rw [← h, ← h']
      abel

lemma biCoeffBaseChange_def (n : ℕ × ℕ) :
    biCoeffBaseChange f sm n = (MvPolynomial.rTensor
      (f.toFun (MvPolynomial (Fin 2) S) ((LinearEquiv.rTensor (R := R) (M × M')
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
            (X 0 ⊗ₜ[R] (compFstRight R S S M M') sm + X 1 ⊗ₜ[R] (compSndRight R S S M M') sm)))))
            ((finTwoArrowEquiv' ℕ).symm n) := by
  simp [biCoeffBaseChange_apply, map_add]

variable {S' : Type*} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S')

theorem biGenerizeBaseChange_rTensor :
    biGenerizeBaseChange ((LinearMap.rTensor (M × M') φ.toLinearMap) sm) =
      LinearMap.rTensor _ (mapAlgHom φ).toLinearMap (biGenerizeBaseChange sm) := by
  induction sm using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>  simp [rTensor_tmul, biGenerizeBaseChange_apply_tmul, smul_tmul',
      smul_eq_C_mul, mapAlgHom_apply]
  | add x y hx hy => simp [map_add, ← hx, ← hy]

theorem rTensor_biCoeffBaseChange_eq :
    (LinearMap.rTensor N φ.toLinearMap) (biCoeffBaseChange f sm n) =
      biCoeffBaseChange f ((LinearMap.rTensor (M × M') φ.toLinearMap) sm) n := by
  simp [biCoeffBaseChange, biGenerizeBaseChange_rTensor, ← f.isCompat_apply,
    rTensor_finsuppLeft_eq, Finsupp.ofSupportFinite_coe]

end Coefficients

end PolynomialLaw
