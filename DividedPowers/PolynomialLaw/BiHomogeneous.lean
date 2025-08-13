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
    f.ground ((r.1 • m.1, r.2 • m.2)) = (r.1^n.1 * r.2^n.2) • f.ground m := by
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

theorem isBiHomogeneousOfBiDegreeOneZero_biCoeff
    (hf : f.IsBiHomogeneousOfDegree (1, 0)) (m : M × M') {d : ℕ × ℕ}
    (hd : d ≠ (1, 0)) : (biCoeff m f) d = 0 :=
  isBiHomogeneousOfDegree_biCoeff hf m hd

theorem isBiHomogeneousOfBiDegreeZeroOne_biCoeff
    (hf : f.IsBiHomogeneousOfDegree (0, 1)) (m : M × M') {d : ℕ × ℕ}
    (hd : d ≠ (0, 1)) : (biCoeff m f) d = 0 :=
  isBiHomogeneousOfDegree_biCoeff hf m hd

#exit

theorem isMultiHomogeneousOfDegreeOne_coeff_support_le {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f).support ⊆ Finset.map
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [Finsupp.mem_support_iff, ne_eq] at hd
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and]
  exact ⟨i, ((not_imp_comm.mp (isMultiHomogeneousOfMultiDegreeOne_coeff i hf m)) hd).symm⟩

theorem isMultiHomogeneousOfMultiDegreeOne_coeff_single {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f) (Finsupp.single i 1) = f.ground (Pi.single i (m i)) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : Finset.sum Finset.univ (fun (j : ι) ↦ (Pi.single i (1 : R) j) ⊗ₜ[R] Pi.single j (m j)) =
      1 ⊗ₜ[R] Pi.single i (m i) := by
    rw [Finset.sum_eq_single i (fun _ _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_tmul])
      (fun hi => by simp [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same]
  simp only [← this, toFun_sum_tmul_eq_multiCoeff_sum, map_finsuppSum, lid_tmul]
  rw [sum_of_support_subset _ (isMultiHomogeneousOfDegreeOne_coeff_support_le i hf m) _ (by simp),
    Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_eq_single i _ (by simp)]
  · rw [Finset.prod_eq_single i (fun j _ hj => by rw [single_eq_of_ne hj.symm, pow_zero])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same,
      one_pow, _root_.one_smul]
  · intro j _ hj
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_univ _)
      (by simp only [single_eq_same, pow_one, Pi.single_eq_of_ne hj]),
      _root_.zero_smul]

end

section Components

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

open MvPolynomial

variable {S : Type*} [CommSemiring S] [Algebra R S]

variable (ι R S M)

-- **MI**: we need to rename these.

private noncomputable def el_S_hom :
    (S ⊗[R] Π i, M i) →ₗ[R] MvPolynomial ι R ⊗[R] (S ⊗[R] (Π i, M i)) where
  toFun := fun m ↦ ∑ (i : ι), (X i) ⊗ₜ (compRight R S S M i m)
  map_add' m m'  := by simp [map_add, ← Finset.sum_add_distrib, tmul_add]
  map_smul' r m := by simp [Finset.smul_sum]

private noncomputable def el_S'_hom :
    (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι R ⊗[R] S) ⊗[R] (Π i, M i) :=
  (TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm.comp (el_S_hom ι R M S)

private noncomputable def el_S''_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι S) ⊗[R] (Π i, M i) :=
  (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv).comp (el_S'_hom ι R M S)

variable {ι R M S}

private lemma el_S_hom_apply_tmul (s : ι → S) (m : Π i, M i) :
    el_S_hom ι R M S ((piRight R R _ _ ).symm (fun i ↦ s i ⊗ₜ m i)) =
      ∑ (i : ι), (X i) ⊗ₜ (s i ⊗ₜ (Pi.single i (m i))) := by
  simp only [el_S_hom, TensorProduct.compRight, singleRight, projRight, coe_comp,
    LinearEquiv.coe_coe, coe_single, coe_proj, coe_piRight, Function.comp_apply,
    Function.eval, coe_mk, AddHom.coe_mk]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [LinearEquiv.apply_symm_apply, piRight_symm_single]

private lemma el_S'_hom_apply_tmul (s : ι → S) (m : Π i, M i) :
    el_S'_hom ι R M S ((piRight R R _ _ ).symm (fun i ↦ s i ⊗ₜ m i)) =
      ∑ (i : ι), (X i) ⊗ₜ s i ⊗ₜ (Pi.single i (m i)) := by
  simp [el_S'_hom, coe_piRight_symm, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    el_S_hom_apply_tmul, map_sum, assoc_symm_tmul]

private lemma el_S''_hom_apply_tmul (s : ι → S) (m : Π i, M i) :
    el_S''_hom ι R M S ((piRight R R _ _ ).symm (fun i ↦ s i ⊗ₜ m i)) =
      ∑ (i : ι), (C (s i) * (X i)) ⊗ₜ (Pi.single i (m i)) := by
  simp only [el_S''_hom,
    LinearEquiv.coe_rTensor, coe_piRight_symm, coe_comp, Function.comp_apply, el_S'_hom_apply_tmul,
    map_sum, rTensor_tmul, LinearEquiv.coe_coe,
    AlgEquiv.toLinearEquiv_apply, ]
  apply Finset.sum_congr rfl
  intro i _
  congr
  simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply, rTensorAlgHom,
    Algebra.TensorProduct.lift_tmul, mapAlgHom_apply, eval₂_X, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom', algebraMap_eq, Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, map_mul, mapAlgEquiv_apply, map_X, map_C,
    RingHom.coe_coe, Algebra.TensorProduct.lid_tmul, _root_.one_smul]
  rw [mul_comm]

noncomputable def multiGenerize_S (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) :
    MvPolynomial ι S ⊗[R] N := f.toFun (MvPolynomial ι S) (el_S''_hom ι R M S sm)

-- This does not look so useful.
lemma multiGenerize_S_apply_pi_tmul (s : ι → S) (m : Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) :
    multiGenerize_S ((piRight R R _ _ ).symm (fun i ↦ s i ⊗ₜ m i)) f =
      (((multiCoeff m) f).sum fun k n ↦ (∏ i, (C (s i) * X i) ^ k i) ⊗ₜ[R] n) := by
  simp [multiGenerize_S, el_S''_hom_apply_tmul, toFun_sum_tmul_eq_multiCoeff_sum]

noncomputable def multiCoeff_S (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N)
    (n : ι →₀ ℕ) : S ⊗[R] N := MvPolynomial.rTensor (multiGenerize_S sm f) n

lemma multiCoeff_S_apply' (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S sm f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (piRight R S S _).symm
      (Pi.single (M := fun i ↦ S ⊗[R] M i) i (piRight R S S _ sm i)))))) n := by
  simp only [multiCoeff_S, multiGenerize_S, el_S''_hom, el_S'_hom, el_S_hom,
    TensorProduct.compRight, singleRight, projRight, coe_comp, LinearEquiv.coe_coe, coe_single, coe_proj, Function.comp_apply,
    Function.eval, coe_mk, AddHom.coe_mk, map_sum]

lemma multiCoeff_S_apply (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S sm f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (TensorProduct.compRight R S S M i) sm)))) n := rfl

lemma multiCoeff_S_apply_tmul (s : S) (m : Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S (s ⊗ₜ m) f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (s ⊗ₜ (Pi.single i (m i))))))) n := by
  rw [multiCoeff_S_apply]
  congr
  simp [TensorProduct.compRight, singleRight, projRight]

-- This does not look so useful.
lemma multiCoeff_S_apply_pi_tmul (s : ι → S) (m : Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) :
    multiCoeff_S ((piRight R R _ _ ).symm (fun i ↦ s i ⊗ₜ m i)) f =
      MvPolynomial.rTensor (((multiCoeff m) f).sum
        fun k n ↦ (∏ i, (C (s i) * X i) ^ k i) ⊗ₜ[R] n) := by
  unfold multiCoeff_S
  ext d
  simp [multiGenerize_S_apply_pi_tmul]

variable (s : Π (_ : ι), S) (m : Π i, M i)

/- /-- `LinearEquiv.lTensor M f : M ⊗ N ≃ₗ M ⊗ P` is the natural linear equivalence
induced by `f : N ≃ₗ P`. -/
def lTensor (f : N ≃ₗ[R] P) : M ⊗[R] N ≃ₗ[R] M ⊗[R] P := TensorProduct.congr (refl R M) f

/-- `LinearEquiv.rTensor M f : N₁ ⊗ M ≃ₗ N₂ ⊗ M` is the natural linear equivalence
induced by `f : N₁ ≃ₗ N₂`. -/
def rTensor (f : N ≃ₗ[R] P) : N ⊗[R] M ≃ₗ[R] P ⊗[R] M := TensorProduct.congr f (refl R M)

variable (g : P ≃ₗ[R] Q) (f : N ≃ₗ[R] P) (m : M) (n : N) (p : P) (x : M ⊗[R] N) (y : N ⊗[R] M)

@[simp] theorem coe_lTensor : lTensor M f = (f : N →ₗ[R] P).lTensor M := rfl

@[simp] theorem coe_lTensor_symm : (lTensor M f).symm = (f.symm : P →ₗ[R] N).lTensor M := rfl

@[simp] theorem coe_rTensor : rTensor M f = (f : N →ₗ[R] P).rTensor M := rfl-/

theorem _root_.LinearEquiv.rTensor_apply {R : Type*} [CommSemiring R] (M : Type*) {N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (f : N ≃ₗ[R] P) (nm : N ⊗[R] M) :
    LinearEquiv.rTensor M f nm = (f : N →ₗ[R] P).rTensor M nm := rfl

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
