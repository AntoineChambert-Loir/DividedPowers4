/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.ForMathlib.Algebra.MvPolynomial.Lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Basic
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Pi
import DividedPowers.PolynomialLaw.Homogeneous
import DividedPowers.PolynomialLaw.MultiCoeff
import Mathlib.Data.Finsupp.Weight

universe u uι

/- # Multihomogeneous components of a polynomial map

Let `S` be an `R`-algebra and let `j : S →ₐ[S] S[X]` be the canonical algebra map.

For `m : S ⊗[R] M`, we consider the element `X • (j m) : S[X] ⊗[R] M`
and its image `f.toFun' S[X] (X • (j m)) : S[X] ⊗[R] N`.
The components of `f` are defined so that
`f.toFun' S[X] (X • (j m)) = ∑ X ^ p • (j ((f.multiComponent n).toFun' S m))`.

If one consider the morphism of evaluation at 1, `ε : S[X] →ₐ[R] S`,
we have `ε ∘ j = @id S`, and the compatibility properties of `f` implies that
`f.toFun' S[X] m = ∑ (f.multiComponent n).toFun' S m`.
-/

open LinearMap TensorProduct

noncomputable section

namespace PolynomialLaw

section MultiHomogeneous

section

open Finsupp MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {N : Type*}
  [AddCommMonoid N] [Module R N] (n : ι →₀ ℕ) (r : R) {f g : (Π i, M i) →ₚₗ[R] N}

-- TODO: fix docstring
/-- A polynomial map `f : Π (i : ι), M i →ₚ[R] N` is multihomogeneous of multidegree `n : ι →₀ ℕ`
  if for all families `{z_i : R ⊗ M i}_{i : ι}`, `{r_i : R}_{i : ι}`, one has
  `f (r_1 • z_1, r_2 • z_2, ...) = Π i r_i^(n i) • f (z_1, z_2, ...)`. -/
def IsMultiHomogeneousOfDegree (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : ι → S) (m : S ⊗ ((i : ι) → M i)),
    f.toFun' S (∑ i, r i • TensorProduct.compRight R S S M i m) =
      (∏ i, r i ^ n i) • f.toFun' S m

theorem IsMultiHomogeneousOfDegree_add (hf : f.IsMultiHomogeneousOfDegree n)
    (hg : g.IsMultiHomogeneousOfDegree n) : (f + g).IsMultiHomogeneousOfDegree n :=
  fun S _ _ s m ↦ by simp [-piRight_apply, add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsMultiHomogeneousOfDegree_smul (hf : f.IsMultiHomogeneousOfDegree n) :
    (r • f).IsMultiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp [smul_def, Pi.smul_apply, hf S, smul_comm r]

/-- The submodule of homogeneous polynomial laws of degree `p`. -/
def multiGrade (n : ι →₀ ℕ) : Submodule R ((Π i, M i) →ₚₗ[R] N) where
  carrier            := IsMultiHomogeneousOfDegree n
  add_mem' hf hg     := IsMultiHomogeneousOfDegree_add n hf hg
  smul_mem' r f hf   := IsMultiHomogeneousOfDegree_smul n r hf
  zero_mem' S _ _ r _:= by simp [zero_def, smul_zero]

lemma mem_multiGrade : f ∈ multiGrade n ↔ IsMultiHomogeneousOfDegree n f := by rfl

-- TODO: golf
/-- If `f` is multihomogeneous of multidegree `n`, then all `f.toFun S` are multihomogeneous of
  multidegree `n`. -/
lemma isMultiHomogeneousOfDegree_toFun {n : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S)
    (m : S ⊗[R] (Π i, M i)) :
    f.toFun S (∑ i, r i • TensorProduct.compRight R S S M i m) =
      (∏ i, (r i)^(n i)) • f.toFun S m := by
  choose d ψ m' r' hm' hr' using PolynomialLaw.exists_lift'' m r
  simp only [← hr', ← hm', ← map_pow, ← map_prod, ← isCompat_apply, toFun_eq_toFun', smul_rTensor]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  simp only [TensorProduct.compRight, singleRight, projRight, coe_comp, LinearEquiv.coe_coe,
    coe_single, coe_proj, Function.comp_apply, Function.eval,]
  apply congr_arg
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← smul_rTensor]
  congr
  rw [LinearEquiv.symm_apply_eq]
  ext j
  simp only [piRight_rTensor_eq_rTensor_piRight', LinearEquiv.apply_symm_apply]
  by_cases hij : j = i
  · rw [hij, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero]

/-- If `f` is multihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isMultiHomogeneousOfDegree_ground {n : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (r : ι → R) (m : (Π i, M i)) :
    f.ground (r • m) = (∏ i, (r i)^(n i)) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (Π i, M i)).symm m)
  simp only [lid_symm_apply] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply, ← map_smul, ← hfrm]
  congr
  rw [right_ext_iff R]
  intro i
  simp_rw [map_sum, projRight_compRight]
  simp [projRight]

theorem IsMultiHomogeneousOfDegree.comp {P : Type*} [AddCommMonoid P] [Module R P]
    {f : (Π i, M i) →ₚₗ[R] N} {g : N →ₚₗ[R] P} {p : ι →₀ ℕ} {q : ℕ}
    (hf : f.IsMultiHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsMultiHomogeneousOfDegree (q • p) := by
  intro S _ _ r m
  simp [comp_toFun', Function.comp_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_comm q, pow_mul, Finset.prod_pow, Pi.smul_apply, hf S, hg S]

theorem IsMultiHomogeneousOfMultiDegree.isHomogeneousOfDegree {f : (Π i, M i) →ₚₗ[R] N} {n : ι →₀ ℕ}
    (hf : f.IsMultiHomogeneousOfDegree n) : f.IsHomogeneousOfDegree n.degree := by
  intro S _ _ r m
  rw [degree_eq_sum, ← Finset.prod_pow_eq_pow_sum, ← hf S (fun i ↦ r) m, ← Pi.smul_def]
  simp [Pi.smul_apply, ← Finset.smul_sum, sum_compRight]

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isMultiHomogeneousOfDegree_multiCoeff {n d : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (m : Π i, M i) (hd : d ≠ n) :
    PolynomialLaw.multiCoeff m f d = 0 := by
  have hf' := isMultiHomogeneousOfDegree_toFun hf
  specialize hf' (MvPolynomial ι R) (fun i ↦ X i)
    (∑ i, (1 : MvPolynomial ι R) ⊗ₜ[R] Pi.single i (m i))
  simp only [map_sum, compRight_tmul, singleRight_tmul] at hf'
  have : (∑ x, X (R := R) x • ∑ x_1, (1 : MvPolynomial ι R) ⊗ₜ[R]
    Pi.single x (Pi.single x_1 (m x_1) x)) =
      (∑ x, X (R := R) x • (1 : MvPolynomial ι R) ⊗ₜ[R] Pi.single x (m x)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_eq_single x (fun _ _ hy ↦ by rw [Pi.single_eq_of_ne (Ne.symm hy), Pi.single_zero,
      tmul_zero]) (fun hx' ↦ absurd hx hx'), Pi.single_eq_same]
  simp_rw [this, smul_tmul', smul_eq_mul] at hf'
  rw [toFun_sum_tmul_eq_multiCoeff_sum, toFun_sum_tmul_eq_multiCoeff_sum] at hf'
  simp only [smul_sum, smul_tmul', smul_eq_mul, ] at hf'
  let φ : MvPolynomial ι R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp (LinearMap.rTensor N (lcoeff R d))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [mul_one, map_finsuppSum, one_pow, Finset.prod_const_one] at hφ
  rw [Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  · simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul,
      LinearMap.coe_mk, AddHom.coe_mk, lid_tmul, φ, prod_X_pow_eq_monomial', coeff_monomial,
      ↓reduceIte, _root_.one_smul, ite_smul, _root_.zero_smul, left_eq_ite_iff] at hφ
    exact hφ (Ne.symm hd)
  · intro k hk0 hkd
    simp [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, lcoeff_apply, φ,
      prod_X_pow_eq_monomial', coeff_monomial, if_neg (Ne.symm hd)]
  · intro k hk0 hkd
    simp [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, lcoeff_apply, φ,
      prod_X_pow_eq_monomial', coeff_monomial, if_neg hkd]

theorem toFun_zero_of_constantCoeff_zero (hf : coeff (0 : ι → Π i, M i) f = 0) (S : Type*)
    [CommSemiring S] [Algebra R S] : f.toFun S 0 = 0 := by
  have : (0 : S ⊗[R] (Π i, M i)) = ∑ i, (0 : S) ⊗ₜ[R] Pi.single i (0 : M i) := by simp
  rw [this, toFun_sum_tmul_eq_coeff_sum]
  simp only [sum, Pi.single_zero]
  conv_rhs => rw [← Finset.sum_const_zero (s := ( ((coeff (0 : ι → Π i, M i)) f).support))]
  apply Finset.sum_congr rfl
  erw [hf]
  simp

theorem toFun'_zero_of_constantCoeff_zero (hf : coeff (0 : ι → Π i, M i) f = 0) (S : Type u)
    [CommSemiring S] [Algebra R S] : f.toFun' S 0 = 0 := by
  rw [← toFun_eq_toFun', toFun_zero_of_constantCoeff_zero hf]


/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isMultiHomogeneousOfDegree_of_multiCoeff_iff' (p : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    IsMultiHomogeneousOfDegree p f ↔ ∀ (m : Π i, M i) (n : ι →₀ ℕ) (_ : n ≠ p),
      PolynomialLaw.multiCoeff m f n = 0 := by
  refine ⟨fun hf m n hn ↦ isMultiHomogeneousOfDegree_multiCoeff hf m hn, fun H S _ _ r μ => ?_⟩
  induction μ using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, smul_zero, Finset.sum_const_zero]
    sorry
  | tmul s m =>
    conv_rhs => rw [← sum_compRight (S := S) (s ⊗ₜ m)]
    simp [compRight_tmul, singleRight_tmul, ← toFun_eq_toFun', smul_tmul',
      toFun_sum_tmul_eq_multiCoeff_sum, smul_sum]
    apply Finsupp.sum_congr
    intro d hd
    have hd' : p = d := sorry
    rw [hd']
    congr
    simp [mul_pow, Finset.prod_mul_distrib]
  | add sm sm' hsm hsm' =>
    simp only [map_add, smul_add]
    sorry -- **MI**: unclear

theorem isMultiHomogeneousOfMultiDegreeOne_multiCoeff {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) {d : ι →₀ ℕ}
    (hd : d ≠ Finsupp.single i 1) : (multiCoeff m f) d = 0 :=
  isMultiHomogeneousOfDegree_multiCoeff hf m hd

theorem isMultiHomogeneousOfDegreeOne_multiCoeff_support_le {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f).support ⊆ Finset.map
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [Finsupp.mem_support_iff, ne_eq] at hd
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and]
  exact ⟨i, ((not_imp_comm.mp (isMultiHomogeneousOfMultiDegreeOne_multiCoeff i hf m)) hd).symm⟩

theorem isMultiHomogeneousOfMultiDegreeOne_multiCoeff_single {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f) (Finsupp.single i 1) = f.ground (Pi.single i (m i)) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : Finset.sum Finset.univ (fun (j : ι) ↦ (Pi.single i (1 : R) j) ⊗ₜ[R] Pi.single j (m j)) =
      1 ⊗ₜ[R] Pi.single i (m i) := by
    rw [Finset.sum_eq_single i (fun _ _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_tmul])
      (fun hi => by simp [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same]
  simp only [← this, toFun_sum_tmul_eq_multiCoeff_sum, map_finsuppSum, lid_tmul]
  rw [sum_of_support_subset _ (isMultiHomogeneousOfDegreeOne_multiCoeff_support_le i hf m) _
    (by simp), Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_eq_single i _ (by simp)]
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
    TensorProduct.compRight, singleRight, projRight, coe_comp, LinearEquiv.coe_coe, coe_single,
    coe_proj, Function.comp_apply, Function.eval, coe_mk, AddHom.coe_mk, map_sum]

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

end MultiHomogeneous

end PolynomialLaw
