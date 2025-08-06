/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.PolynomialLaw.Homogeneous
import DividedPowers.PolynomialLaw.MultiCoeff
import DividedPowers.ForMathlib.Algebra.MvPolynomial.Lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Multilinear.Basic

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
    f.toFun' S ((piRight R S S M).symm fun i ↦ r i • (piRight R R S M) m i) =
      (∏ i, r i ^ n i) • f.toFun' S m

theorem IsMultiHomogeneousOfDegree_add (hf : f.IsMultiHomogeneousOfDegree n)
    (hg : g.IsMultiHomogeneousOfDegree n) : (f + g).IsMultiHomogeneousOfDegree n :=
  fun S _ _ s m ↦ by simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsMultiHomogeneousOfDegree_smul (hf : f.IsMultiHomogeneousOfDegree n) :
    (r • f).IsMultiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm _ _ _

/-- The submodule of homogeneous polynomial laws of degree `p`. -/
def multiGrade (n : ι →₀ ℕ) : Submodule R ((Π i, M i) →ₚₗ[R] N) where
  carrier            := IsMultiHomogeneousOfDegree n
  add_mem' hf hg     := IsMultiHomogeneousOfDegree_add n hf hg
  smul_mem' r f hf   := IsMultiHomogeneousOfDegree_smul n r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_multiGrade : f ∈ multiGrade n ↔ IsMultiHomogeneousOfDegree n f := by rfl

/-- If `f` is multihomogeneous of multidegree `n`, then all `f.toFun S` are multihomogeneous of
  multidegree `n`. -/
lemma isMultiHomogeneousOfDegree_toFun {n : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S)
    (m : S ⊗[R] (Π i, M i)) :
    f.toFun S ((TensorProduct.piRight R S _ _).symm
      (fun i ↦ r i • ((TensorProduct.piRight R S _ _ ) m) i)) =
      (∏ i, (r i)^(n i)) • f.toFun S m := by
  choose d ψ m' r' hm' hr' using PolynomialLaw.exists_lift'' m r
  simp only [← hr', ← hm', ← map_pow, ← map_prod, ←
    isCompat_apply, toFun_eq_toFun', smul_rTensor]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  apply congr_arg
  rw [LinearEquiv.symm_apply_eq]
  ext i
  simp only [piRight_rTensor_eq_rTensor_piRight', smul_rTensor]
  congr
  apply smul_piRight_apply

/-- If `f` is multihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isMultiHomogeneousOfDegree_ground {n : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (r : ι → R) (m : (Π i, M i)) :
    f.ground (r • m) = (∏ i, (r i)^(n i)) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (Π i, M i)).symm m)
  simp only [lid_symm_apply, piRight_apply, piRightHom_tmul] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply]
  rw [← map_smul, ← hfrm]
  congr
  simp only [← tmul_smul, piRight_symm_apply]
  rfl

theorem IsMultiHomogeneousOfDegree.comp {P : Type*} [AddCommMonoid P] [Module R P]
    {f : (Π i, M i) →ₚₗ[R] N} {g : N →ₚₗ[R] P} {p : ι →₀ ℕ} {q : ℕ}
    (hf : f.IsMultiHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsMultiHomogeneousOfDegree (q • p) := by
  intro S _ _ r m
  have hf' := hf S r m/- hf S r m, hg S, -/
  simp only [piRight_apply, coe_piRightHom] at hf'
  have hg' := hg S
  simp only [piRight_apply, comp_toFun', Function.comp_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_comm q, pow_mul, Finset.prod_pow, Pi.smul_apply, hf', hg']

theorem IsMultiHomogeneousOfDegree.isHomogeneousOfDegree {f : (Π i, M i) →ₚₗ[R] N} {n : ι →₀ ℕ}
    (hf : f.IsMultiHomogeneousOfDegree n) : f.IsHomogeneousOfDegree n.degree := by
  intro S _ _ r m
  rw [degree_eq_sum, ← Finset.prod_pow_eq_pow_sum, ← hf S (fun i ↦ r) m, ← Pi.smul_def,
    ← coe_piRight R S, smul_const_piRight_apply, LinearEquiv.symm_apply_apply]

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isMultiHomogeneousOfDegree_multiCoeff {n : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (m : Π i, M i) (d : ι →₀ ℕ) (hd : d ≠ n) :
    PolynomialLaw.multiCoeff m f d = 0 := by
  classical
  let μ : MvPolynomial ι R ⊗[R] (Π i, M i) :=
    Finset.univ.sum (fun i => X i ⊗ₜ[R] Pi.single i (m i))
  have hf' := isMultiHomogeneousOfDegree_toFun hf (MvPolynomial ι R) (fun i ↦ X i) μ

  /- have : (fun i ↦ ∑ c, X (R := R) c ⊗ₜ[R] Pi.single c (m c) i) =
    (∑ c, fun i ↦ X (R := R) c ⊗ₜ[R] Pi.single c (m c) i) := by rw [@Finset.sum_fn] -/

  simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply,
    coe_piRight_symm,  toFun_sum_tmul_eq_multiCoeff_sum, μ, Finset.smul_sum,
    ← Finset.sum_fn] at hf'

  --wrong
  have (x : ι) : ((piRight R R (MvPolynomial ι R) M).symm fun a ↦
      (X a * X x) ⊗ₜ[R] Pi.single x (m x) a) =
      (∑ a, ((X a * X x) ⊗ₜ[R] Pi.single x (m x))) := by

    have hinj : Function.Injective (piRight R R (MvPolynomial ι R) M) := sorry
    rw [← Function.Injective.eq_iff hinj]
    simp only [coe_piRight_symm, LinearEquiv.apply_symm_apply, map_sum, piRight_apply,
      piRightHom_tmul]
    rw [Finset.sum_fn]
    ext a
    rw [Finset.sum_eq_single a]
    · intro b _ hb
      rw [Pi.single_eq_of_ne]
      sorry
      sorry
    · sorry

  simp only [smul_tmul', smul_eq_mul] at hf'
  /- have (i : ι) : X (R := R) i • ∑ c, X (R := R) c ⊗ₜ[R] Pi.single c (m c) i =
      (∑ c, X (R := R) i • X (R := R) c ⊗ₜ[R] Pi.single c (m c) i) := by
    rw [Finset.smul_sum]
    sorry -/
  --simp_rw [Pi.single_apply] at hf'

  sorry
  /- simp only [multiCoeff, multiGenerize, coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk,
    AddHom.coe_mk, Function.comp_apply]
  simp only [scalarRTensor_apply, EmbeddingLike.map_eq_zero_iff] -/
  /- classical
  let μ : MvPolynomial ι R ⊗[R] (Π i, M i) :=
    Finset.univ.sum (fun i => X i ⊗ₜ[R] Pi.single i (m i))
  have hf' := isMultiHomogeneousOfDegree_toFun hf (MvPolynomial ι R) (fun i ↦ X i) μ

  /- have : (fun i ↦ ∑ c, X (R := R) c ⊗ₜ[R] Pi.single c (m c) i) =
    (∑ c, fun i ↦ X (R := R) c ⊗ₜ[R] Pi.single c (m c) i) := by rw [@Finset.sum_fn] -/

  simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply,
    coe_piRight_symm,  toFun_sum_tmul_eq_multiCoeff_sum, μ] at hf' -/


 /-  simp only [← Finset.sum_fn, map_sum, piRight_symm_apply] at hf'
  rw [toFun_sum_tmul_eq_multiCoeff_sum] at hf'
   -/
/-

  let e (b : ι →₀ ℕ) (k : ℕ) : Option ι →₀ ℕ :=
    Finsupp.update (Finsupp.mapDomainEmbedding (Function.Embedding.some) b) none k
  have he : ∀ b k, (X none ^ k * (Finset.prod Finset.univ
      fun x => X (Option.some x) ^ b x) : MvPolynomial (Option ι) R) = monomial (e b k) 1 := fun b k ↦ by
    simp only [Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply, monomial_eq,
      map_one, Finsupp.prod_pow, Finsupp.coe_update, Fintype.prod_option, Function.update_self,
      ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, one_mul, e]
    exact congr_arg₂ _ rfl (Finset.prod_congr rfl (fun _ _ => by
      rw [Finsupp.mapDomain_apply (Option.some_injective ι)]))
  have he_some : ∀ b k i, e b k (some i) = b i := fun b k i ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, reduceCtorEq, ↓reduceDIte,
      Finsupp.mapDomain_apply (Option.some_injective ι), e]
  have he_none : ∀ b k, k = e b k none := fun b k ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, ↓reduceDIte, e]
   /-  On écrit l'homogénéité : f (∑ T ⬝ X_i m_i) = T ^ p ⬝ f(∑ X_i m_i)
   ∑ coeff f e (T X) ^ e = T ^ p ⬝ ∑ coeff f e X ^ e
   Identification : (coeff f e) T^|e| X^ e = coeff f e T ^ p X ^ e
   On en déduit coeff f e = 0 si |e| ≠ p .    -/
  let μ : MvPolynomial (Option ι) R ⊗[R] (Π i, M i) :=
    Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m)
  have hf' := isMultiHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (fun i ↦ X none) μ
  simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply, Finset.smul_sum, smul_tmul',
    smul_eq_mul, coe_piRight_symm, μ] at hf'
  simp only [toFun_sum_tmul_eq_coeff_sum,
    Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [Finset.prod_pow_eq_pow_sum] at hφ
  /- simp only [map_finsuppSum, LinearMap.map_smul, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hφ -/
  sorry/- rw [Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
    AddHom.coe_mk, lid_tmul, φ] at hφ
  rw [he, coeff_monomial, if_pos, _root_.one_smul, he, coeff_monomial, if_neg, _root_.zero_smul]
    at hφ
  exact hφ
  · intro hd'
    apply hd
    convert (DFunLike.ext_iff.mp hd'.symm) none <;> exact (he_none _ _)
  · simp only [Finset.mem_univ, forall_true_left, implies_true,
      Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  all_goals
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
      AddHom.coe_mk, lid_tmul, φ]
    rw [he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i  -/ -/

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isMultiHomogeneousOfDegree_multiCoeff' {n : ι →₀ ℕ} {f : (Π i, M i) →ₚₗ[R] N}
    (hf : IsMultiHomogeneousOfDegree n f) (m : Π i, M i) (d : ι →₀ ℕ) (hd : d ≠ n) :
    PolynomialLaw.multiCoeff m f d = 0 := by
  classical
  let e (b : ι →₀ ℕ) (k : ℕ) : Option ι →₀ ℕ :=
    Finsupp.update (Finsupp.mapDomainEmbedding (Function.Embedding.some) b) none k
  have he : ∀ b k, (X none ^ k * (Finset.prod Finset.univ
      fun x => X (Option.some x) ^ b x) : MvPolynomial (Option ι) R) = monomial (e b k) 1 := fun b k ↦ by
    simp only [Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply, monomial_eq,
      map_one, Finsupp.prod_pow, Finsupp.coe_update, Fintype.prod_option, Function.update_self,
      ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, one_mul, e]
    exact congr_arg₂ _ rfl (Finset.prod_congr rfl (fun _ _ => by
      rw [Finsupp.mapDomain_apply (Option.some_injective ι)]))
  have he_some : ∀ b k i, e b k (some i) = b i := fun b k i ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, reduceCtorEq, ↓reduceDIte,
      Finsupp.mapDomain_apply (Option.some_injective ι), e]
  have he_none : ∀ b k, k = e b k none := fun b k ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, ↓reduceDIte, e]
   /-  On écrit l'homogénéité : f (∑ T ⬝ X_i m_i) = T ^ p ⬝ f(∑ X_i m_i)
   ∑ coeff f e (T X) ^ e = T ^ p ⬝ ∑ coeff f e X ^ e
   Identification : (coeff f e) T^|e| X^ e = coeff f e T ^ p X ^ e
   On en déduit coeff f e = 0 si |e| ≠ p .    -/
  let μ : MvPolynomial (Option ι) R ⊗[R] (Π i, M i) :=
    Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m)
  have hf' := isMultiHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (fun i ↦ X none) μ
  simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply, Finset.smul_sum, smul_tmul',
    smul_eq_mul, coe_piRight_symm, μ] at hf'
  simp only [toFun_sum_tmul_eq_coeff_sum,
    Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [Finset.prod_pow_eq_pow_sum] at hφ
  /- simp only [map_finsuppSum, LinearMap.map_smul, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hφ -/
  sorry/- rw [Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
    AddHom.coe_mk, lid_tmul, φ] at hφ
  rw [he, coeff_monomial, if_pos, _root_.one_smul, he, coeff_monomial, if_neg, _root_.zero_smul]
    at hφ
  exact hφ
  · intro hd'
    apply hd
    convert (DFunLike.ext_iff.mp hd'.symm) none <;> exact (he_none _ _)
  · simp only [Finset.mem_univ, forall_true_left, implies_true,
      Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  all_goals
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
      AddHom.coe_mk, lid_tmul, φ]
    rw [he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i  -/

/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isMultiHomogeneousOfDegree_of_coeff_iff (p : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    IsMultiHomogeneousOfDegree p f ↔ ∀ (m : Π i, M i) (n : ι →₀ ℕ) (_ : n ≠ p),
      PolynomialLaw.multiCoeff m f n = 0 := by
  refine ⟨fun hf m n hn ↦ isMultiHomogeneousOfDegree_multiCoeff hf m n hn, fun H S _ _ r μ => ?_⟩
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
  have (i : ι) : r i • (piRight R R S M) (∑ i, s i ⊗ₜ[R] m i) i =
      (piRight R R S M) (∑ j, (r i • s j) ⊗ₜ[R] m j) i := by
    simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply,
      Finset.smul_sum, TensorProduct.smul_tmul']
  simp_rw [this]
  simp_rw [coe_piRight_symm,/-  LinearEquiv.symm_apply_apply -/]
  simp only [smul_eq_mul, map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply]
  rw [← toFun_eq_toFun',toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum]
  simp_rw [← Finset.sum_fn]
  simp only [map_sum, coe_piRight_symm]
  /- simp only [piRight, LinearEquiv.ofLinear_symm_apply] -/
  have : (∑ x, (piRight R R S M).symm fun a ↦ (r a * s x) ⊗ₜ[R] m x a) =
    (∑ x, (piRight R R S M).symm (∑ a, Pi.single a ((r a * s x) ⊗ₜ[R] m x a))) := by
    congr
    simp only [coe_piRight_symm, map_sum, piRight_symm_single]
    ext x
    sorry

  simp_rw [this]
  simp only [map_sum, piRight_symm_single]
  have : ∑ x, ∑ x_1, (r x_1 * s x) ⊗ₜ[R] Pi.single x_1 (m x x_1) =
    ∑ x_1, ∑ x, (r x_1 * s x) ⊗ₜ[R] Pi.single x_1 (m x x_1) := by rw [@Finset.sum_comm]
  --
  simp_rw [this]


  --rw [toFun_sum_tmul_eq_coeff_sum]

  /- simp_rw [this]
  simp only [piRight_symm_apply]
  simp_rw [smul_tmul', toFun_sum_tmul_eq_coeff_sum] -/
  sorry

theorem toFun'_zero_of_constantCoeff_zero
    (f : ((i : ι) → M i) →ₚₗ[R] N) (hf : coeff (0 : ι → Π i, M i) f = 0)
    (S : Type u) [CommSemiring S] [Algebra R S] :
    f.toFun' S 0 = 0 := by
  have : (0 : S ⊗[R] (Π i, M i)) = ∑ i, (0 : S) ⊗ₜ[R] Pi.single i (0 : M i) := by simp
  rw [this, ← toFun_eq_toFun', toFun_sum_tmul_eq_coeff_sum]
  simp only [sum, Pi.single_zero]
  conv_rhs => rw [← Finset.sum_const_zero (s := ( ((coeff (0 : ι → Π i, M i)) f).support))]
  congr
  ext d
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := sorry
  have h0 : ∏ i, (0 : S) ^ d i = 0 := sorry
  rw [h0, zero_tmul]

/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isMultiHomogeneousOfDegree_of_coeff_iff' (p : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    IsMultiHomogeneousOfDegree p f ↔ ∀ (m : Π i, M i) (n : ι →₀ ℕ) (_ : n ≠ p),
      PolynomialLaw.multiCoeff m f n = 0 := by
  refine ⟨fun hf m n hn ↦ isMultiHomogeneousOfDegree_multiCoeff hf m n hn, fun H S _ _ r μ => ?_⟩
  induction μ using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.zero_apply,
      smul_zero, piRight_symm_zero]
    --extract_goal
    sorry
  | add =>
    simp only [piRight_apply, coe_piRightHom, map_add, Pi.add_apply, smul_add, coe_piRight_symm]
    sorry
  | tmul s m =>
    simp only [piRight_apply, piRightHom_tmul, coe_piRight_symm]
    have : ((piRight R R S M).symm fun i ↦ r i • s ⊗ₜ[R] m i) =
      (piRight R R S M).symm (∑ i, Pi.single i (r i • s ⊗ₜ[R] m i)) := by
      sorry
    rw [this]
    simp only [map_sum, coe_piRight_symm]
    have (x : ι) : (piRight R R S M).symm (Pi.single x (r x • s ⊗ₜ[R] m x)) =
       (r x • s) ⊗ₜ[R] (Pi.single x (m x)) := by
      rw [smul_tmul', piRight_symm_single]
    simp_rw [this]
    have hsm : s ⊗ₜ m = (∑ x, s ⊗ₜ[R] Pi.single x (m x)) := sorry
    rw [← toFun_eq_toFun', toFun_sum_tmul_eq_multiCoeff_sum, hsm,
      toFun_sum_tmul_eq_multiCoeff_sum]
    simp [Finsupp.sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [Finsupp.mem_support_iff] at hd
    have hpd: p = d := sorry -- use H
    rw [hpd]
    simp only [smul_tmul', smul_eq_mul]
    congr
    sorry

theorem isMultiHomogeneousOfMultiDegreeOne_coeff {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) {d : ι →₀ ℕ}
    (hd : d ≠ Finsupp.single i 1) : (multiCoeff m f) d = 0 :=
  isMultiHomogeneousOfDegree_multiCoeff hf m d hd

theorem isMultiHomogeneousOfDegreeOne_coeff_support_le {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f).support ⊆ Finset.map
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [Finsupp.mem_support_iff, ne_eq] at hd
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
    true_and]
  exact ⟨i, ((not_imp_comm.mp (isMultiHomogeneousOfMultiDegreeOne_coeff i hf m)) hd).symm⟩

theorem _root_.MvPolynomial.prod_X_pow_eq_monomial' {R : Type u} {σ : Type u_1} [Fintype σ]
    {s : σ →₀ ℕ} [CommSemiring R] : ∏ x, X (R := R) x ^ s x = (monomial s) 1 := by
  rw [← prod_X_pow_eq_monomial]
  apply Finset.prod_congr_of_eq_on_inter _ (fun _ _ ha ↦ absurd (Finset.mem_univ _) ha)
    (fun _ _ _ ↦ rfl )
  intro _ _ ha
  rw [Finsupp.mem_support_iff, not_not] at ha
  rw [ha, pow_zero]

theorem isMultiHomogeneousOfMultiDegreeOne_coeff_single {f : (Π i, M i) →ₚₗ[R] N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f) (Finsupp.single i 1) = f.ground (Pi.single i (m i)) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  simp only [multiCoeff, multiGenerize, coe_comp, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  --simp only [scalarRTensor_apply, EmbeddingLike.apply_eq_iff_eq]
  simp only [toFun_sum_tmul_eq_multiCoeff_sum]
  simp only [map_finsuppSum, Finsupp.sum_apply, scalarRTensor_apply, rTensor_tmul, lcoeff_apply,
    lid_tmul]
  let r : ι → R := Function.const ι 1
  have : (1 : R) = (Function.const ι 1) i := rfl

  sorry
  /- rw [this, toFun_tmul_eq_multiCoeff_sum]
  simp only [Finsupp.sum, Function.const_apply, one_pow, map_sum, lid_tmul, _root_.one_smul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [isMultiHomogeneousOfDegree_of_coeff_iff] at hf
  --simp? [coeff_single_X_pow]
  have hd' : d = Finsupp.single i 1 := sorry
  simp only [hd']
  rw [MvPolynomial.prod_X_pow_eq_monomial']
  simp only [coeff_monomial, ↓reduceIte, _root_.one_smul] -/

end

section Components

-- I need `ι : Type u` to be able to apply `f.toFun'`.
-- Update: I changed to `ι : Type*` and using `toFun`.
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

open MvPolynomial

variable {S : Type*} [CommSemiring S] [Algebra R S]

variable (ι R S M)

noncomputable def el_S_hom : (S ⊗[R] Π i, M i) →ₗ[R] MvPolynomial ι R ⊗[R] (S ⊗[R] (Π i, M i)) where
  toFun := fun m ↦ ∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
    (Pi.single (M := fun i ↦  S ⊗[R] M i) i (TensorProduct.piRight R R S _ m i))
  map_add' m m'  := by
    simp only [piRight_apply, map_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← TensorProduct.tmul_add]
    congr
    simp only [Pi.single_add, map_add]
  map_smul' r m := by
    simp only [map_smul, piRight_apply, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← tmul_smul, Pi.single_smul, map_smul]

noncomputable def el_S'_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι R ⊗[R] S) ⊗[R] (Π i, M i) :=
  (TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm.comp (el_S_hom ι R M S)

noncomputable def el_S''_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι S) ⊗[R] (Π i, M i) :=
  (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv).comp (el_S'_hom ι R M S)

variable {ι R M S}

noncomputable def multiGenerize_S (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) :
    MvPolynomial ι S ⊗[R] N := f.toFun (MvPolynomial ι S) (el_S''_hom ι R M S sm)

noncomputable def multiCoeff_S (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N)
    (n : ι →₀ ℕ) : S ⊗[R] N := MvPolynomial.rTensor (multiGenerize_S sm f) n

lemma multiCoeff_S_apply (sm : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S sm f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
      (Pi.single (M := fun i ↦ S ⊗[R] M i) i (TensorProduct.piRight R R S _ sm i)))))) n := rfl

lemma multiCoeff_S_apply_tmul (s : S) (m : Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S (s ⊗ₜ m) f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
      (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
      ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
      (∑ (i : ι), (X i) ⊗ₜ (s ⊗ₜ (Pi.single i (m i))))))) n := by
  rw [multiCoeff_S_apply]
  congr
  simp

variable (s : Π (_ : ι), S) (m : Π i, M i)

-- **MI**: perhaps `Nontrivial R` can be removed, with an alternative argument in that case.
lemma multiCoeff_S_apply_smul [Nontrivial R] (s : Π _, S) (sm : S ⊗[R] Π i, M i)
    (f : (Π i, M i) →ₚₗ[R] N) (n : ι →₀ ℕ) :
    multiCoeff_S ((TensorProduct.piRight R R S _).symm
      (fun i ↦ (s i) • ((TensorProduct.piRight R R S _) sm i))) f n =
      (∏ i, (s i) ^ n i) • multiCoeff_S (sm) f n  := by
  let ψ := ((aeval (R := S) (fun i ↦ (C (s i) * X i : MvPolynomial ι S))).restrictScalars R)
  suffices ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (∑ i,
              X i ⊗ₜ[R]
                (piRight R R S M).symm
                  (Pi.single i ((piRight R R S M)
                   ((piRight R R S M).symm fun i ↦ s i • (piRight R R S M) sm i) i)))))
                   =
    ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap)
      ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (∑ i,
              X i ⊗ₜ[R]
                (piRight R R S M).symm
                  (Pi.single i ((piRight R S S M) sm i)))))) by
    simp only [multiCoeff_S_apply,]
    simp_rw [this, ← f.isCompat_apply]
    clear this
    simp only [← coe_piRight R S]
    generalize  ht : (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i, X i ⊗ₜ[R] (piRight R R S M).symm (Pi.single i ((piRight R S S M) sm i)))))) = t

    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (∏ i, s i ^ n i)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    apply symm
    dsimp only [LinearMap.rTensor, TensorProduct.map]
    apply TensorProduct.lift.unique
    intro f k
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, lift.tmul,
      lcoeff_apply, mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply,
      TensorProduct.smul_tmul']
    apply congr_arg₂ _ _ rfl
    -- ψ f = f (s • X)
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | monomial k' a =>
        simp only [ψ, coeff_monomial]
        split_ifs with h
        · rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial,
           algebraMap_eq]
          rw [coeff_C_mul]
          simp only [Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib]
          simp_rw [← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_pos rfl]
          simp
        · simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, algebraMap_eq]
          rw [coeff_C_mul]
          simp only [Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib]
          simp_rw [← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_neg h]
          simp
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap)
    ((LinearMap.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv.toLinearMap)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X i ⊗ₜ[R]
          (piRight R R S M).symm
            (Pi.single i ((piRightHom R S S M) sm i)))))

  simp only [AlgEquiv.toLinearEquiv_toLinearMap, ← rTensor_comp_apply]
  simp only [LinearEquiv.apply_symm_apply]

  induction sm using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.ofNat_apply, smul_zero, Pi.single_zero,
      tmul_zero]
  | tmul t m =>
    have hi (i : ι) : s i • (piRight R S S M) (t ⊗ₜ[R] m) i =
       (piRight R R S M) ((s i * t) ⊗ₜ[R] m) i := by
      simp [smul_tmul']
    rw [← coe_piRight R S]
    simp_rw [hi]
    simp only [piRight_apply, piRightHom_tmul, piRight_symm_single,
      assoc_symm_tmul, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, rTensor_tmul,
      coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply]

    simp only [AlgHom.coe_restrictScalars', ψ]
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      ]
    congr
    simp only [rTensorAlgHom_apply_eq, rTensor_apply_tmul]
    simp only [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X i) := rfl
    simp only [this, support_X, Finset.mem_singleton] at hd
    simp only [hd]
    simp only [MvPolynomial.aeval_def]
    simp only [mapAlgEquiv_apply, algebraMap_eq, eval₂_map]
    simp only [eval₂, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Finsupp.prod_pow,
      map_zero, zero_mul, Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]

    simp only [X, ← single_eq_monomial, Finsupp.single_eq_same, _root_.one_smul]

    rw [Finset.prod_eq_single i]
    simp only [Finsupp.single_eq_same, pow_one]
    simp only [single_eq_monomial, map_monomial, RingHom.coe_coe, Algebra.TensorProduct.lid_tmul,
      _root_.one_smul]
    simp only [mul_comm (s i) t, C_mul_monomial, mul_one]

    · intro j _ hj
      rw [Finsupp.single_eq_of_ne (Ne.symm hj), pow_zero]
    · intro hj
      exact absurd (Finset.mem_univ _) hj

  | add sm sm' h h' =>
    simp only [map_add, Pi.add_apply, smul_add]
    simp only [Pi.single_add, map_add, tmul_add, h, h']

lemma multiCoeff_S_def (m : S ⊗[R] Π i, M i) (f : (Π i, M i) →ₚₗ[R] N) :
    multiCoeff_S m f = (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))) := by
  ext n
  simp only [multiCoeff_S_apply, piRight_apply, map_sum]

/- Here we define the multihomogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

-- **MI**: this proof is really slow.
theorem bar (n : ι →₀ ℕ) (f : ((i : ι) → M i) →ₚₗ[R] N) {S' : Type*} [CommSemiring S']
    [Algebra R S'] (φ : S →ₐ[R] S')
    (sm : S ⊗[R] ((i : ι) → M i)) :
    (LinearMap.rTensor N φ.toLinearMap) (multiCoeff_S sm f n) =
    multiCoeff_S ((LinearMap.rTensor ((i : ι) → M i) φ.toLinearMap) sm) f n := by
  simp only [multiCoeff_S_def, rTensor_apply, ← rTensor_comp_apply]
  rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply, map_sum]
  congr 3
  ext i
  induction sm using TensorProduct.induction_on with
  | zero => simp [map_zero, Pi.single_zero, tmul_zero]
  | tmul s m =>
      simp only [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul, rTensor_tmul,
        AlgHom.toLinearMap_apply]
      apply foo
  | add sm sm' hsm hsm' =>
      simp [map_add, Pi.add_apply, Pi.single_add, tmul_add, ← hsm, ← hsm']

/- The multihomogeneous component of degree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def multiComponent (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    (Π i, M i) →ₚₗ[R] N where
  toFun' S _ _ := fun m ↦ multiCoeff_S m f n
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    apply bar

theorem multiComponent.toFun'_apply (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)
  (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
  (f.multiComponent n).toFun' S m = multiCoeff_S m f n := rfl

-- **MI**: I replaced  `CommRing S` by `CommSemiring S` and `S : Type u` by `S : Type*`.
theorem multiComponent_toFun_apply (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (f.multiComponent n).toFun S m = multiCoeff_S m f n := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, multiComponent.toFun'_apply]
  exact bar n f ψ q

lemma multiComponentIsMultiHomogeneous [Nontrivial R] (n : ι →₀ ℕ) (f : (Π i, M i) →ₚₗ[R] N) :
    IsMultiHomogeneousOfDegree n (multiComponent n f) := by
  simp only [multiComponent]
  intro S _ _ s sm
  rw [coe_piRight_symm]
  exact multiCoeff_S_apply_smul s sm f n

theorem multiComponent_add (n : ι →₀ ℕ) (f g : (Π i, M i) →ₚₗ[R] N) :
    (f + g).multiComponent n = f.multiComponent n + g.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, multiCoeff_S_apply, piRight_apply, map_sum, add_toFun_apply, map_add,
    Finsupp.coe_add, Pi.add_apply, add_def]

theorem multiComponent_smul (n : ι →₀ ℕ) (r : R) (f : (Π i, M i) →ₚₗ[R] N) :
    (r • f).multiComponent n = r • f.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, multiCoeff_S_apply, piRight_apply, map_sum, smul_toFun, Pi.smul_apply,
    rTensor_apply, map_smul, smul_def]

-- Perhaps I should just use `ι →₀ ℕ` everywhere, but since I am usually assuming `Fintype ι`,
-- this seemed redundant.
-- For now, I used it in the def. of `multiComponent` to avoid this error:
/- ... has Finset (ι →₀ ℕ) : Type u but is expected to have type Set (ι → ℕ) : Type u-/
 theorem support_multiComponent' (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun' S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))).support := by
  ext n
  simp [multiComponent, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, multiCoeff_S_def]

-- **MI**: I replaced  `CommRing S` by `CommSemiring S`.
theorem support_multiComponent (f : (Π i, M i) →ₚₗ[R] N) {S : Type*} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))).support := by
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
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x)))))) := by
  ext n
  simp only [multiComponent, multiCoeff_S_apply, piRight_apply, map_sum, Finsupp.ofSupportFinite_coe]

open Finsupp

-- TODO: golf, extract lemmas
theorem asdf (S : Type u) [CommSemiring S] [Algebra R S] (s : S) (m : (i : ι) → M i) :
  s ⊗ₜ[R] m =
    ∑ i, (aeval 1) (scalarRTensorAlgEquiv (X i ⊗ₜ[R] s)) ⊗ₜ[R] Pi.single i (m i) := by
  by_cases hR : Nontrivial R
  · have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
    conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    simp only [rTensorAlgHom_apply_eq]

    simp only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul]
    simp only [Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    have : Finsupp.support (X (R := R) i) = {Finsupp.single i 1} := by
      rw [← support_X (R := R)]; rfl

    rw [this]
    simp only [Finset.sum_singleton, map_zero, Finsupp.prod_single_index, mul_one,
      Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]
    have : s = (1 : R) • s := by simp only [_root_.one_smul]
    convert this
    rw [X]
    simp only [monomial, AddMonoidAlgebra.lsingle, Finsupp.lsingle, Finsupp.singleAddHom,
      ZeroHom.toFun_eq_coe, ZeroHom.coe_mk]
    change (Finsupp.single (Finsupp.single i 1) 1) (Finsupp.single i 1) = 1
    simp only [Finsupp.single_eq_same]
  · simp only [nontrivial_iff, ne_eq, not_exists, not_not] at hR
    have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
    conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    simp only [rTensorAlgHom_apply_eq]

    simp only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul]
    simp only [Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    have : Finsupp.support (X (R := R) i) = ∅ := by
      have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X (R := R) i) := by
        rw [MvPolynomial.support] --TODO: lemma
      classical rw [this, X, support_monomial, if_pos (hR 1 0)]
    rw [this]
    simp only [Finset.sum_empty, Finsupp.sum_zero_index]
    have h1 : (1 : S) = algebraMap R S 1 := by simp only [map_one]
    rw [← mul_one s, ← map_one (algebraMap R S), hR 1 0, map_zero, mul_zero]

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
        (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) sm x))))) := by
    simp only [map_sum]
    simp only [LinearMap.rTensor]
    induction sm using TensorProduct.induction_on with
    | zero =>  simp [map_zero, Pi.single_zero, tmul_zero, Finset.sum_const_zero]
    | tmul s m =>
        simp only [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul]
        simp only [LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_tmul,
          AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', id_coe, id_eq]
        apply asdf
    | add sm₁ sm₂ hsm₁ hsm₂ => simp [map_add, Pi.add_apply, Pi.single_add, tmul_add, Finset.sum_add_distrib,
        ← hsm₁, ← hsm₂]
  conv_rhs => rw [← toFun_eq_toFun', hsm', ← f.isCompat_apply]
  generalize f.toFun (MvPolynomial ι S)
    (∑ x,
            (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
              ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
                (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) sm x))))) = sn
  convert rTensor'_sum (A := R) (fun _ ↦ 1) sn
  · simp only [_root_.one_smul]
  · ext p
    simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', aeval_eq_eval₂Hom,
      Algebra.algebraMap_self, coe_eval₂Hom, eval₂_id, eval_eq, Pi.ofNat_apply, one_pow,
      Finset.prod_const_one, mul_one, MvPolynomial.lsum, coe_restrictScalars, lsmul_apply,
      smul_eq_mul, one_mul, LinearMap.coe_mk, AddHom.coe_mk]
    rfl

end Components

end MultiHomogeneous

end PolynomialLaw
