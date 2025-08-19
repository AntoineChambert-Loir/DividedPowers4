import DividedPowers.PolynomialLaw.Basic2
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

open MvPolynomial TensorProduct

universe u

variable (R : Type u) [CommSemiring R] (M M' : Type*) [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] {N : Type*} [AddCommGroup N] [Module R N]
  (f : M →ₚₗ[R] N) (n p : ℕ)

namespace PolynomialLaw

section Prod

/-- `fst R M M'` is the polynomial law `M × M' →ₚₗ[R] M` obtained by prolonging the
`i`th canonical projection. -/
def fst : M × M' →ₚₗ[R] M where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.fst R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma fst_apply (m : M × M') : fst R M M' m = m.1 := by simp [fst, ground_apply]

lemma fst_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (fst R M M').toFun' S m =
    ((TensorProduct.prodRight R R S M  M') m).fst := by
  simp only [fst, TensorProduct.prodRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

lemma fst_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (fst R M M').toFun S m =
    ((TensorProduct.prodRight R R S M  M') m).fst := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (fst R M M').isCompat_apply, PolynomialLaw.toFun_eq_toFun']
  simp only [fst_toFun'_apply, prodRight_rTensor_fst_eq_rTensor_prodRight]

/-- `fst R M M'` is the polynomial law `M × M' →ₚₗ[R] M` obtained by prolonging the
`i`th canonical projection. -/
def snd : M × M' →ₚₗ[R] M' where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.snd R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma snd_apply (m : M × M') : snd R M M' m = m.2 := by simp [snd, ground_apply]

lemma snd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (snd R M M').toFun' S m =
    ((TensorProduct.prodRight R R S M  M') m).snd := by
  simp only [snd, TensorProduct.prodRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul => simp
  | add m m' hm hm' => simp [hm, hm']

lemma snd_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M')} : (snd R M M').toFun S m =
    ((TensorProduct.prodRight R R S M  M') m).snd := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (snd R M M').isCompat_apply, PolynomialLaw.toFun_eq_toFun']
  simp only [snd_toFun'_apply, prodRight_rTensor_snd_eq_rTensor_prodRight]

/-- `sum_proj R M ι` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] M` defined as the sum of all the
coordinate laws from  `(Π (_ : ι), M)`to `M`. -/
def sum_fst_snd : M × M →ₚₗ[R] M := fst R M M + snd R M M

lemma sum_fst_snd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M)} : (sum_fst_snd R M).toFun' S m =
    ((TensorProduct.prodRight R R S M M) m).fst +
      ((TensorProduct.prodRight R R S M M) m).snd := by
  rw [sum_fst_snd, TensorProduct.prodRight]
  simp only [add_def, Pi.add_apply, fst_toFun'_apply, snd_toFun'_apply, LinearEquiv.ofLinear_apply,
    TensorProduct.AlgebraTensorModule.lift_apply, LinearMap.restrictScalars_comp]
  congr 1

def inl : M →ₚₗ[R] M × M' where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.inl R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma inl_apply (m : M) : inl R M M' m = (m, 0) := by simp [inl, ground_apply]

lemma inl_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M} :
    (inl R M M').toFun' S m = ((TensorProduct.inlRight R R S M M') m) := by
  simp only [inl, TensorProduct.inlRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have h0 : (0 : S ⊗[R] M') = s ⊗ₜ 0 := by simp
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.coe_inl,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h0,
      TensorProduct.prodRight_symm_tmul]
  | add m m' hm hm' =>
    simp [map_add, hm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hm']

lemma inl_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M} :
    (inl R M M').toFun S m = ((TensorProduct.inlRight R R S M M') m) := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (inl R M M').isCompat_apply, PolynomialLaw.toFun_eq_toFun']
  simp only [inl_toFun'_apply, rTensor_inlRight_eq_inlRight_rTensor]

def inr : M' →ₚₗ[R] M × M' where
  toFun' S _ _ := (TensorProduct.map (LinearMap.id (M := S)) (LinearMap.inr R M M'))
  isCompat' φ := by
    ext x
    simp only [Function.comp_apply, LinearMap.rTensor_def, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]

lemma inr_apply (m : M') : inr R M M' m = (0, m) := by simp [inr, ground_apply]

lemma inr_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M'} :
    (inr R M M').toFun' S m = ((TensorProduct.inrRight R R S M M') m) := by
  simp only [inr, TensorProduct.inrRight]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    have h0 : (0 : S ⊗[R] M) = s ⊗ₜ 0 := by simp
    simp only [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, LinearMap.coe_inr,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h0,
      TensorProduct.prodRight_symm_tmul]
  | add m m' hm hm' =>
    simp [map_add, hm, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, hm']

lemma inr_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] {m : TensorProduct R S M'} :
    (inr R M M').toFun S m = ((TensorProduct.inrRight R R S M M') m) := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialLaw.exists_lift m
  rw [← (inr R M M').isCompat_apply, PolynomialLaw.toFun_eq_toFun']
  simp only [inr_toFun'_apply, rTensor_inrRight_eq_inrRight_rTensor]

end Prod
