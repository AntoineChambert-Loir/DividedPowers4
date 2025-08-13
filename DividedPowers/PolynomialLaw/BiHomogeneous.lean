/- Copyright ACL & MIdFF 2024 -/
import DividedPowers.PolynomialLaw.BiCoeff
import DividedPowers.PolynomialLaw.MultiHomogeneous
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod

universe u uι

/- # Bihomogeneous components of a polynomial map

-/

noncomputable section

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R]

variable {M M' N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N] [Module R N]

open LinearMap TensorProduct

section BiHomogeneous

open Finsupp MvPolynomial

open TensorProduct

def IsBiHomogeneousOfDegree (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (s : S × S) (m : S ⊗[R] (M × M')),
    f.toFun' S (s.1 • TensorProduct.compFstRight R S S M M' m +
      s.2 • TensorProduct.compSndRight R S S M M' m) = (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun' S m

theorem IsBiHomogeneousOfDegree_add (n : ℕ × ℕ) {f g : PolynomialLaw R (M × M') N}
    (hf : f.IsBiHomogeneousOfDegree n) (hg : g.IsBiHomogeneousOfDegree n) :
    (f + g).IsBiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsBiHomogeneousOfDegree_smul (n : ℕ × ℕ) (r : R) {f : PolynomialLaw R (M × M') N}
    (hf : f.IsBiHomogeneousOfDegree n) :
    (r • f).IsBiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp [smul_def, Pi.smul_apply, hf S, smul_comm r]

/-- The submodule of bihomogeneous polynomial laws of degree `n`. -/
def biGrade (n : ℕ × ℕ) : Submodule R (PolynomialLaw R (M × M') N) where
  carrier            := IsBiHomogeneousOfDegree n
  add_mem' hf hg     := IsBiHomogeneousOfDegree_add n hf hg
  smul_mem' r f hf   := IsBiHomogeneousOfDegree_smul n r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

variable (n : ℕ × ℕ) (f : PolynomialLaw R (M × M') N)

lemma mem_biGrade  :
    f ∈ biGrade n ↔ IsBiHomogeneousOfDegree n f := by rfl

variable {n f}

lemma isBiHomogeneousOfDegree_toFun (hf : IsBiHomogeneousOfDegree n f) (S : Type*) [CommSemiring S]
    [Algebra R S] (s : S × S) (m : S ⊗[R] (M × M')) :
    f.toFun S (s.1 • TensorProduct.compFstRight R S S M M' m +
      s.2 • TensorProduct.compSndRight R S S M M' m) =
      (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun S m := by
  choose d ψ m' r' hm' hr1 hr2 using PolynomialLaw.exists_lift_pair m s
  simp only [← hr1, ← hm', ← hr2, ← map_pow, ← map_mul, ← isCompat_apply, toFun_eq_toFun',
    smul_rTensor]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  simp only [compFstRight, inlRight, fstRight, coe_comp, LinearEquiv.coe_coe, coe_inl, coe_fst,
    Function.comp_apply, compSndRight, inrRight, sndRight, coe_inr, coe_snd]
  apply congr_arg
  simp only [map_add, ← smul_rTensor]
  congr <;>
  rw [LinearEquiv.symm_apply_eq] <;>
  simp [Prod.ext_iff, prodRight_rTensor_fst_eq_rTensor_prodRight',
      LinearEquiv.apply_symm_apply, prodRight_rTensor_snd_eq_rTensor_prodRight']

/-- If `f` is bihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isBiHomogeneousOfDegree_ground (hf : IsBiHomogeneousOfDegree n f) (r : R × R) (m : (M × M')) :
    f.ground ((r.1 • m.1, r.2 • m.2)) = (r.1 ^ n.1 * r.2 ^ n.2) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (M × M')).symm m)
  simp only [lid_symm_apply] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply, ← map_smul, ← hfrm]
  congr
  simp only [prod_right_ext_iff R, map_add, fstRight_compFstRight_eq, fstRight_compSndRight_eq,
    sndRight_compFstRight_eq, sndRight_compSndRight_eq]
  simp [fstRight, sndRight]

theorem IsBiHomogeneousOfDegree.comp {P : Type*} [AddCommMonoid P] [Module R P]
    (hf : f.IsBiHomogeneousOfDegree n) {g : N →ₚₗ[R] P} {q : ℕ}  (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsBiHomogeneousOfDegree (q • n) := by
  intro S _ _ r m
  simp [comp_toFun', Function.comp_apply, hf S, hg S, nsmul_eq_mul, Prod.fst_mul,
    Prod.fst_natCast, Nat.cast_id, mul_comm q, pow_mul, Prod.snd_mul, Prod.snd_natCast, mul_pow]

/-- The bi-coefficients of a homogeneous polynomial map of bi-degree `n` vanish outside of
bi-degree `n`. -/
lemma isBiHomogeneousOfDegree_biCoeff {d : ℕ × ℕ} (hf : IsBiHomogeneousOfDegree n f) (m : M × M')
    (hd : d ≠ n) : PolynomialLaw.biCoeff m f d = 0 := by
  have hf' := isBiHomogeneousOfDegree_toFun hf
  specialize hf' (MvPolynomial (Fin 2) R) (X 0, X 1)
    ((1 : MvPolynomial (Fin 2) R) ⊗ₜ[R] (m.1, 0) + (1 : MvPolynomial (Fin 2) R) ⊗ₜ[R] (0, m.2))
  simp only [map_add, compFstRight_tmul, compSndRight_tmul, inlRight_tmul, inrRight_tmul] at hf'
  simp only [Fin.isValue, Prod.mk_zero_zero, tmul_zero, add_zero, zero_add] at hf'
  have : (X (0 : Fin 2) ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)) =
    ((X 0, X (R := R) (1 : Fin 2)).1 ⊗ₜ[R] (m.1, 0) +
      (X (R := R) 0, X (R := R) 1).2 ⊗ₜ[R] (0, m.2)) := rfl
  have h1 : ((1 : MvPolynomial (Fin 2) R) ⊗ₜ[R] (m.1, 0) + 1 ⊗ₜ[R] (0, m.2)) =
    ((1, (1 : MvPolynomial (Fin 2) R)).1 ⊗ₜ[R] (m.1, 0) +
      ((1 : MvPolynomial (Fin 2) R), 1).2 ⊗ₜ[R] (0, m.2)) := rfl
  simp only [smul_tmul', smul_eq_mul, mul_one] at hf'
  rw [this, h1, toFun_sum_tmul_eq_biCoeff_sum, toFun_sum_tmul_eq_biCoeff_sum] at hf'
  simp only [smul_sum, smul_tmul', smul_eq_mul] at hf'
  have h2' (e : ℕ × ℕ) : X (R := R) (0 : Fin 2) ^ e.1 * X 1 ^ e.2 =
      ∏ (i : Fin 2), X i ^ (finTwoArrowEquiv' ℕ).symm e i := by
    simp [Fin.isValue, Fin.prod_univ_two, finTwoArrowEquiv', ofSupportFinite_coe]
  let φ : MvPolynomial (Fin 2) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R ((finTwoArrowEquiv' ℕ).symm d)))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [Fin.isValue, map_finsuppSum, one_pow, mul_one] at hφ
  rw [Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  · simp only [lcoeff, Fin.isValue, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      rTensor_tmul, LinearMap.coe_mk, AddHom.coe_mk, lid_tmul, φ,
      Fin.isValue, h2', prod_X_pow_eq_monomial', coeff_monomial, _root_.one_smul,
      ite_smul, _root_.one_smul, _root_.zero_smul,] at hφ
    simp only [↓reduceIte, EmbeddingLike.apply_eq_iff_eq, left_eq_ite_iff] at hφ
    exact hφ (by simp [(Ne.symm hd)])
  · intro k hk0 hkd
    simp only [Fin.isValue, h2', prod_X_pow_eq_monomial', coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, rTensor_tmul, lcoeff_apply, coeff_monomial, lid_tmul, ite_smul,
      _root_.one_smul, _root_.zero_smul, φ]
    rw [if_neg (by simp [(Ne.symm hd)])]
  · intro k hk0 hkd
    simp only [Fin.isValue, h2', prod_X_pow_eq_monomial', coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, rTensor_tmul, lcoeff_apply, coeff_monomial, lid_tmul, ite_smul,
      _root_.one_smul, _root_.zero_smul,  φ]
    rw [if_neg (by simp [hkd])]

theorem toFun_zero_of_constantBiCoeff_zero (hf : biCoeff (0 : M × M') f = 0) (S : Type*)
    [CommSemiring S] [Algebra R S] : f.toFun S 0 = 0 := by
  have : (0 : S ⊗[R] (M × M')) = (0 : S) ⊗ₜ[R] ((0 : M), (0 : M')) := by simp
  rw [this, toFun_tmul_fst_eq_biCoeff_sum ((0 : M), (0 : M'))]
  simp only [sum]
  conv_rhs => rw [← Finset.sum_const_zero (s := ((biCoeff (0 : M × M') f).support))]
  apply Finset.sum_congr rfl
  rw [Prod.mk_zero_zero, hf]
  simp

theorem toFun'_zero_of_constantBiCoeff_zero (hf : biCoeff (0 : M × M') f = 0) (S : Type u)
    [CommSemiring S] [Algebra R S] : f.toFun' S 0 = 0 := by
  rw [← toFun_eq_toFun', toFun_zero_of_constantBiCoeff_zero hf]

theorem isBiHomogeneousOfDegree_of_coeff_iff' :
    IsBiHomogeneousOfDegree n f ↔ ∀ (m : M × M') (k : ℕ × ℕ) (_ : k ≠ n),
      PolynomialLaw.biCoeff m f k = 0 := by
  refine ⟨fun hf m n hn ↦ isBiHomogeneousOfDegree_biCoeff hf m hn, fun H S _ _ r μ => ?_⟩
  obtain ⟨p, s, m, rfl⟩ := exists_Fin S μ
  have h1 : r.1 • (compFstRight R S S M M') (∑ i, s i ⊗ₜ[R] m i) =
      (compFstRight R S S M M') (∑ i, (r.1 • s i) ⊗ₜ[R] m i) := by
    simp_rw [← map_smul, Finset.smul_sum, smul_tmul']
  have h2 : r.2 • (compSndRight R S S M M') (∑ i, s i ⊗ₜ[R] m i) =
      (compSndRight R S S M M') (∑ i, (r.2 • s i) ⊗ₜ[R] m i) := by
    simp_rw [← map_smul, Finset.smul_sum, smul_tmul']
  simp_rw [h1, h2]
  simp only [smul_eq_mul, map_sum, compFstRight_tmul, inlRight_tmul, compSndRight_tmul,
    inrRight_tmul]
  rw [← toFun_eq_toFun']
  sorry

theorem isBiHomogeneousOfBiDegree_biCoeff {a b : ℕ} (hf : f.IsBiHomogeneousOfDegree (a, b))
    (m : M × M') {d : ℕ × ℕ} (hd : d ≠ (a, b)) : (biCoeff m f) d = 0 :=
  isBiHomogeneousOfDegree_biCoeff hf m hd

theorem isBiHomogeneousOfBiDegree_biCoeff_support_le {a b : ℕ}
    (hf : f.IsBiHomogeneousOfDegree (a, b)) (m : M × M') :
    (biCoeff m f).support ⊆ {(a, b)} := by
  intro d hd
  by_contra hd'
  exact (Finsupp.mem_support_iff.mp hd)
    (isBiHomogeneousOfBiDegree_biCoeff hf m (Finset.notMem_singleton.mp hd'))

theorem isBiHomogeneousOfMultiDegreeOneZero_biCoeff_eq {a b : ℕ}
    (hf : f.IsBiHomogeneousOfDegree (a, b)) (m : M × M') :
    (biCoeff m f) (a, b) = f.ground m := by
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : (1 : R) ⊗ₜ[R] m = (1, (1 : R)).1 ⊗ₜ[R] (m.1, 0) + ((1 : R), 1).2 ⊗ₜ[R] (0, m.2) := by
    simp [← tmul_add]
  rw [this, toFun_sum_tmul_eq_biCoeff_sum, map_finsuppSum,
    sum_of_support_subset _ (isBiHomogeneousOfBiDegree_biCoeff_support_le hf m) _ (by simp)]
  simp

section Components

open MvPolynomial

variable (S : Type*) [CommSemiring S] [Algebra R S]

variable (R M M')

  --     f.toFun' S (s.1 • TensorProduct.compFstRight R S S M M' m +
 --     s.2 • TensorProduct.compSndRight R S S M M' m) = (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun' S m

private noncomputable def el_S_hom :
    (S ⊗[R] (M × M')) →ₗ[R] MvPolynomial (Fin 2) R ⊗[R] (S ⊗[R] (M × M')) where
  toFun := fun m ↦ (X 0) ⊗ₜ (compFstRight R S S M M' m) + (X 1) ⊗ₜ (compSndRight R S S M M' m)
  map_add' m m'  := by simp only [Fin.isValue, map_add, tmul_add]; abel
  map_smul' r m := by simp

private noncomputable def el_S'_hom :
    (S ⊗[R] (M × M')) →ₗ[R] (MvPolynomial (Fin 2) R ⊗[R] S) ⊗[R] (M × M') :=
  (TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm.comp (el_S_hom R M M' S)

private noncomputable def el_S''_hom :
    (S ⊗[R] (M × M')) →ₗ[R] (MvPolynomial (Fin 2) S) ⊗[R] (M × M') :=
  (LinearEquiv.rTensor (M × M') scalarRTensorAlgEquiv.toLinearEquiv).comp (el_S'_hom R M M' S)

variable {R M M' S}

private lemma el_S_hom_apply_tmul (s : S × S) (m : M × M') :
    el_S_hom R M M' S ((prodRight R R _ _ _).symm ((s.1 ⊗ₜ m.1, s.2 ⊗ₜ m.2))) =
      (X (0 : Fin 2)) ⊗ₜ (s.1 ⊗ₜ (m.1, 0)) + (X (1 : Fin 2)) ⊗ₜ (s.2 ⊗ₜ (0, m.2)) := by
  simp only [el_S_hom, Fin.isValue, compFstRight, inlRight, fstRight, coe_comp, LinearEquiv.coe_coe,
    coe_inl, coe_fst, Function.comp_apply, compSndRight, inrRight, sndRight, coe_inr, coe_snd,
    LinearMap.coe_mk, AddHom.coe_mk, Fin.isValue, coe_prodRight, LinearEquiv.apply_symm_apply]
  simp [prodRight]

private lemma el_S'_hom_apply_tmul (s : S × S) (m : M × M') :
    el_S'_hom R M M' S ((prodRight R R _ _ _).symm ((s.1 ⊗ₜ m.1, s.2 ⊗ₜ m.2))) =
      (X (0 : Fin 2)) ⊗ₜ s.1 ⊗ₜ (m.1, 0) + (X (1 : Fin 2)) ⊗ₜ s.2 ⊗ₜ (0, m.2) := by
  simp [el_S'_hom, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, el_S_hom_apply_tmul,
    Fin.isValue, map_add, assoc_symm_tmul]

private lemma el_S''_hom_apply_tmul (s : S × S) (m : M × M') :
    el_S''_hom R M M' S ((prodRight R R _ _ _).symm ((s.1 ⊗ₜ m.1, s.2 ⊗ₜ m.2))) =
      (C s.1 * X (0 : Fin 2)) ⊗ₜ (m.1, 0) + ( C s.2 * X (1 : Fin 2)) ⊗ₜ (0, m.2) := by
  simp only [el_S''_hom, LinearEquiv.coe_rTensor, AlgEquiv.toLinearEquiv_toLinearMap,
    coe_prodRight_symm, coe_comp, Function.comp_apply, el_S'_hom_apply_tmul, Fin.isValue, map_add,
    rTensor_tmul, AlgEquiv.toLinearMap_apply]
  simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply, rTensorAlgHom,
    Algebra.TensorProduct.lift_tmul, mapAlgHom_apply, eval₂_X, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom', algebraMap_eq, Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, map_mul, mapAlgEquiv_apply, map_X, map_C,
    RingHom.coe_coe, Algebra.TensorProduct.lid_tmul, _root_.one_smul]
  rw [mul_comm, mul_comm (C s.2)]

noncomputable def biGenerize_S (sm : S ⊗[R] (M × M')) (f : (M × M') →ₚₗ[R] N) :
    MvPolynomial (Fin 2) S ⊗[R] N := f.toFun (MvPolynomial (Fin 2) S) (el_S''_hom R M M' S sm)

-- This does not look so useful.
lemma biGenerize_S_apply_pi_tmul (s : S × S) (m : M × M') :
    biGenerize_S ((prodRight R R _ _ _).symm ((s.1 ⊗ₜ m.1, s.2 ⊗ₜ m.2))) f =
      (((biCoeff m) f).sum fun k n ↦ ((C s.1 * X (0 : Fin 2)) ^ k.1 *
        (C s.2 * X (1 : Fin 2)) ^ k.2) ⊗ₜ[R] n) := by
  have : (C s.1 * X (0 : Fin 2)) ⊗ₜ[R] (m.1, 0) + (C s.2 * X 1) ⊗ₜ[R] (0, m.2) =
    (C s.1 * X 0, C s.2 * X (1 : Fin 2)).1 ⊗ₜ[R] (m.1, 0) +
      (C s.1 * X 0, C s.2 * X 1).2 ⊗ₜ[R] (0, m.2) := rfl
  simp [biGenerize_S, el_S''_hom_apply_tmul, this, toFun_sum_tmul_eq_biCoeff_sum m]

variable (sm : S ⊗[R] (M × M')) (f : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ)

noncomputable def biCoeff_S : S ⊗[R] N :=
    MvPolynomial.rTensor (biGenerize_S sm f) ((finTwoArrowEquiv' ℕ).symm n)

variable {sm f n}

-- **MI** : Useless (?)
lemma biCoeff_S_apply' : biCoeff_S sm f n = MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
    (LinearEquiv.rTensor (M × M') scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
        (X 0 ⊗ₜ[R] (prodRight R S S M M').symm (((prodRight R S S M M') sm).1, 0) +
        (X 1 ⊗ₜ[R] (prodRight R S S M M').symm (0, ((prodRight R S S M M') sm).2))))))
          ((finTwoArrowEquiv' ℕ).symm n) := by
  simp only [biCoeff_S, biGenerize_S, el_S''_hom, LinearEquiv.coe_rTensor,
    AlgEquiv.toLinearEquiv_toLinearMap, el_S'_hom, el_S_hom, Fin.isValue, compFstRight, inlRight,
    fstRight, coe_comp, LinearEquiv.coe_coe, coe_inl, coe_fst, Function.comp_apply, compSndRight,
    inrRight, sndRight, coe_inr, coe_snd, LinearMap.coe_mk, AddHom.coe_mk, map_add]
  rfl

lemma biCoeff_S_apply :
    biCoeff_S sm f n = MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
      (LinearEquiv.rTensor (M × M') scalarRTensorAlgEquiv.toLinearEquiv
        ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
          ((X 0) ⊗ₜ (compFstRight R S S M M' sm) + (X 1) ⊗ₜ (compSndRight R S S M M' sm)))))
            ((finTwoArrowEquiv' ℕ).symm n) := rfl

lemma biCoeff_S_apply_tmul (s : S) (m : M × M') :
    biCoeff_S (s ⊗ₜ m) f n = MvPolynomial.rTensor (f.toFun (MvPolynomial (Fin 2) S)
      (LinearEquiv.rTensor (M × M') scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
      (((X 0) ⊗ₜ (compFstRight R S S M M' (s ⊗ₜ (m.1, 0))) +
        (X 1) ⊗ₜ (compSndRight R S S M M' (s ⊗ₜ (0, m.2))))))))
      ((finTwoArrowEquiv' ℕ).symm n) := by
  rw [biCoeff_S_apply]
  congr 5
  simp [compFstRight, compSndRight, inlRight, inrRight, fstRight, sndRight]

variable (s : S × S) (m : M × M')

-- This does not look so useful.
lemma biCoeff_S_apply_prod_tmul (n : ℕ × ℕ) :
    biCoeff_S ((prodRight R R _ _ _).symm (s.1 ⊗ₜ m.1, s.2 ⊗ₜ m.2)) f n =
      (MvPolynomial.rTensor (((biCoeff m) f).sum
        fun k n ↦ ((C s.1 * X (0 : Fin 2)) ^ k.1 * (C s.2 * X 1) ^ k.2) ⊗ₜ[R] n))
          ((finTwoArrowEquiv' ℕ).symm n) := by
  unfold biCoeff_S
  simp [biGenerize_S_apply_pi_tmul]

#exit

lemma multiCoeff_S_apply_smul [Nontrivial R] (s : Π _, S) (sm : S ⊗[R] Π i, M i)
    (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S (∑ i, s i • (TensorProduct.compRight R S S M i) sm) f n =
      (∏ i, s i ^ n i) • multiCoeff_S sm f n := by
  let ψ := ((aeval (R := S) (fun i ↦ (C (s i) * X i : MvPolynomial ι S))).restrictScalars R)
  suffices ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (∑ i, X i ⊗ₜ[R] (TensorProduct.compRight R S S M i)
            (∑ i, s i • (TensorProduct.compRight R S S M i) sm))))  =
      ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap)
        ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (∑ i, X i ⊗ₜ[R] (TensorProduct.compRight R S S M i) sm)))) by
    simp only [multiCoeff_S_apply, this, ← f.isCompat_apply]
    clear this
    generalize ht : (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i, X i ⊗ₜ[R] (TensorProduct.compRight R S S M i) sm)))) = t
    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (∏ i, s i ^ n i)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
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
        split_ifs with h
        · rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial,
           algebraMap_eq, coeff_C_mul, Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_pos rfl]
          simp
        · simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, algebraMap_eq]
          rw [coeff_C_mul, Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_neg h]
          simp
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearEquiv.rTensor_apply, AlgEquiv.toLinearEquiv_toLinearMap, ← rTensor_comp_apply]
  induction sm using TensorProduct.induction_on with
  | zero => simp [map_zero, smul_zero, Finset.sum_const_zero, tmul_zero]
  | tmul t m =>
    simp only [compRight_tmul, ← map_smul, compRight_singleRight]
    simp only [map_smul, singleRight_tmul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      assoc_symm_tmul, rTensor_tmul, coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
      AlgHom.toLinearMap_apply]
    rw [smul_tmul', TensorProduct.assoc_symm_tmul]
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_toLinearMap, smul_eq_mul, rTensor_tmul,
      coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply, AlgEquiv.trans_apply, AlgHom.coe_restrictScalars', ψ]
    congr
    simp only [rTensorAlgHom_apply_eq, rTensor_apply_tmul, Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X i) := rfl
    simp only [this, support_X, Finset.mem_singleton] at hd
    simp only [hd, MvPolynomial.aeval_def, algebraMap_eq, eval₂_map]
    simp only [eval₂, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Finsupp.prod_pow,
      map_zero, zero_mul, Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul, X,
      ← single_eq_monomial, Finsupp.single_eq_same, _root_.one_smul]
    rw [Finset.prod_eq_single i (fun _ _ hj ↦ by rw [Finsupp.single_eq_of_ne (Ne.symm hj),
      pow_zero]) (fun hj ↦ absurd (Finset.mem_univ _) hj)]
    simp [single_eq_monomial, mul_comm (s i) t, C_mul_monomial,]
  | add sm sm' h h' => simp only [map_add, smul_add, Finset.sum_add_distrib, tmul_add, h, h']

lemma multiCoeff_S_def (m : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) :
    multiCoeff_S m f = (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x, (LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (TensorProduct.compRight R S S M x m)))))) := by
  ext n
  simp [multiCoeff_S_apply, map_sum]

/- Here we define the multihomogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

--set_option profiler true in
-- **MI**: this proof is still slow.
theorem rTensor_multiCoeff_S_eq (n : ι →₀ ℕ) (f : ((i : ι) → M i) →ₚₗ[R] N) {S' : Type*}
    [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') (sm : S ⊗[R] ((i : ι) → M i)) :
    (LinearMap.rTensor N φ.toLinearMap) (multiCoeff_S sm f n) =
      multiCoeff_S ((LinearMap.rTensor ((i : ι) → M i) φ.toLinearMap) sm) f n := by
  simp only [multiCoeff_S_def, rTensor_apply, ← rTensor_comp_apply]
  rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply, map_sum]
  congr
  ext i
  induction sm using TensorProduct.induction_on with
  | zero => simp [map_zero, tmul_zero]
  | tmul s m =>
      simp only [compRight_tmul, singleRight_tmul, assoc_symm_tmul, LinearEquiv.rTensor_tmul,
        AlgEquiv.toLinearEquiv_apply, rTensor_tmul, AlgHom.toLinearMap_apply]
      exact baseChange_comp_scalarRTensorAlgEquiv_tmul φ s m i
  | add sm sm' hsm hsm' =>
      simp [map_add, tmul_add, ← hsm, ← hsm']

/- The multihomogeneous component of degree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def multiComponent (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    (Π i, M i) →ₚₗ[R] N where
  toFun' S _ _ := fun m ↦ multiCoeff_S m f n
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    apply rTensor_multiCoeff_S_eq

theorem multiComponent.toFun'_apply (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)
    (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (f.multiComponent n).toFun' S m = multiCoeff_S m f n := rfl

theorem multiComponent_toFun_apply (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (f.multiComponent n).toFun S m = multiCoeff_S m f n := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, multiComponent.toFun'_apply]
  exact rTensor_multiCoeff_S_eq n f ψ q

lemma multiComponentIsMultiHomogeneous [Nontrivial R] (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    IsMultiHomogeneousOfDegree n (multiComponent n f) :=
  fun _ _ _ s sm ↦ multiCoeff_S_apply_smul s sm f n

theorem multiComponent_add (n : ι →₀ ℕ) (f g : (Π i, M i) →ₚₗ[R] N) :
    (f + g).multiComponent n = f.multiComponent n + g.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, multiCoeff_S_apply, map_sum, add_toFun_apply, map_add, Finsupp.coe_add,
    Pi.add_apply, add_def]

theorem multiComponent_smul (n : ι →₀ ℕ) (r : R) (f : (Π i, M i) →ₚₗ[R] N) :
    (r • f).multiComponent n = r • f.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, multiCoeff_S_apply, map_sum, smul_toFun, Pi.smul_apply, rTensor_apply,
    map_smul, smul_def]

 theorem support_multiComponent' (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun' S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (compRight R S S M x m)))))).support := by
  ext n
  simp [multiComponent, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, multiCoeff_S_def]

theorem support_multiComponent (f : (Π i, M i) →ₚₗ[R] N) {S : Type*} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x, (LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (compRight R S S M x m)))))).support := by
  ext i
  rw [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_iff_not,
    multiComponent_toFun_apply, multiCoeff_S_def]

theorem LocFinsupp_multiComponent (f : (Π i, M i) →ₚₗ[R] N) :
    LocFinsupp (fun n ↦ f.multiComponent n) := fun S _ _ m ↦ by
  rw [support_multiComponent']
  exact Finset.finite_toSet _

 theorem LocFinsupp_multiComponent_eq (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (Finsupp.ofSupportFinite (fun i => (multiComponent i f).toFun' S m)
      (LocFinsupp_multiComponent f S m)) =
    MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (compRight R S S M x m))))) := by
  ext n
  simp [multiComponent, multiCoeff_S_apply,  map_sum, Finsupp.ofSupportFinite_coe]

open Finsupp

/- theorem _root_.MvPolynomial.not_nontrivial_of_not_nontrivial {ι R : Type*} [CommSemiring R]
    (hR : ¬ Nontrivial R) :
    ¬ Nontrivial (MvPolynomial ι R) := by
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  intro p q
  ext d
  apply hR -/

/- theorem _root_.MvPolynomial.support_eq_empty_of_trivial {ι : Type u_1}
  {R : Type u} [inst_2 : CommSemiring R]
  (hR : ∀ (x x_1 : R), x = x_1) (i : ι) :
  (X (R := R) i).support = ∅ := by
  classical rw [X, support_monomial, if_pos (hR 1 0)] -/

theorem _root_.MvPolynomial.nontrivial_iff_nontrivial (ι R : Type*) [CommSemiring R] :
    Nontrivial R ↔ Nontrivial (MvPolynomial ι R) := by
  refine ⟨fun h ↦ nontrivial_of_nontrivial ι R , ?_⟩
  contrapose
  intro hR
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  intro p q
  ext d
  apply hR

theorem _root_.Algebra.not_nontrivial_of_not_nontrivial (R S : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] (hR : ¬ Nontrivial R) : ¬ Nontrivial S := by
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  have hs (s : S) : s = 0 := by
    rw [← mul_one s, ← map_one (algebraMap R S), hR 1 0, map_zero, mul_zero]
  intro s t
  rw [hs s, hs t]

theorem  _root_.TensorProduct.not_nontrivial_of_not_nontrivial (R S M : Type*) [CommSemiring R]
    [AddCommMonoid M] [Module R M] [CommSemiring S] [Algebra R S] (hS : ¬ Nontrivial S) :
    ¬ Nontrivial (S ⊗[R] M) := by
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  have h (sm : S ⊗[R] M) : sm = 0 := by
    rw [← _root_.one_smul S sm, hS 1 0, _root_.zero_smul]
  intro sm sm'
  rw [h sm, h sm']

-- TODO: golf, extract lemmas
theorem tmul_eq_aeval_sum (S : Type*) [CommSemiring S] [Algebra R S] (s : S) (m : (i : ι) → M i) :
    s ⊗ₜ[R] m =
      ∑ i, (aeval 1) (scalarRTensorAlgEquiv (X i ⊗ₜ[R] s)) ⊗ₜ[R] Pi.single i (m i) := by
  have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
  by_cases hR : Nontrivial R
  · conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply, rTensorAlgHom_apply_eq, aeval_def, Algebra.algebraMap_self, eval₂_map,
      RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul, Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    rw [finsupp_support_eq_support, support_X (R := R)]
    simp only [Finset.sum_singleton, map_zero, Finsupp.prod_single_index, mul_one,
      Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]
    simp [X, ← single_eq_monomial, single_eq_same]
  · have hSM := TensorProduct.not_nontrivial_of_not_nontrivial R S (Π i, M i)
      (Algebra.not_nontrivial_of_not_nontrivial R S hR)
    simp only [nontrivial_iff, ne_eq, not_exists, not_not] at hSM
    apply hSM

/-- A polynomial law is the locally finite sum of its homogeneous components.
(PolynomialLaw lies in between the direct sum and the product of its graded submodules,
hence there is no graded module structure.) -/
theorem recompose_multiComponent {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type u}
  [CommSemiring R] {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (f : (Π i, M i) →ₚₗ[R] N) :
    PolynomialLaw.lfsum (fun n ↦ f.multiComponent n) = f := by
  ext S _ _ sm
  rw [lfsum_eq_of_locFinsupp (LocFinsupp_multiComponent f), LocFinsupp_multiComponent_eq]
  have hsm' : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor (Π i, M i) (∑ x,
    (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X x ⊗ₜ[R] TensorProduct.compRight R S S M x sm))) := by
    simp only [map_sum, LinearMap.rTensor]
    induction sm using TensorProduct.induction_on with
    | zero =>  simp [map_zero, tmul_zero, Finset.sum_const_zero]
    | tmul s m =>
      simp only [compRight_tmul, singleRight_tmul, assoc_symm_tmul, LinearEquiv.rTensor_tmul,
        AlgEquiv.toLinearEquiv_apply, map_tmul, AlgHom.toLinearMap_apply,
        AlgHom.coe_restrictScalars', id_coe, id_eq]
      apply tmul_eq_aeval_sum
    | add sm₁ sm₂ hsm₁ hsm₂ => simp [map_add, tmul_add, Finset.sum_add_distrib, ← hsm₁, ← hsm₂]
  conv_rhs => rw [← toFun_eq_toFun', hsm', ← f.isCompat_apply]
  generalize f.toFun (MvPolynomial ι S)
    (∑ x, (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X x ⊗ₜ[R] TensorProduct.compRight R S S M x sm))) = sn
  convert rTensor'_sum (A := R) (fun _ ↦ 1) sn
  · simp [_root_.one_smul]
  · ext p
    simp [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', aeval_eq_eval₂Hom, eval_eq,
      Finset.prod_const_one, MvPolynomial.lsum, coe_restrictScalars, LinearMap.coe_mk,
      AddHom.coe_mk, Finsupp.sum, MvPolynomial.coeff, finsupp_support_eq_support]

end Components


end BiHomogeneous
