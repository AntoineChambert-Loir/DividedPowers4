/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.ForMathlib.Algebra.MvPolynomial.Lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Basic
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod
import DividedPowers.PolynomialLaw.BiCoeff
import DividedPowers.PolynomialLaw.Homogeneous

universe u v uι

/- # Bihomogeneous components of a polynomial law

Let `R` be a commutative ring, let `M` and `N` be `R`-modules, and let `f : M →ₚₗ[R] N` be a
polynomial law.

## Main Definitions

* `PolynomialLaw.IsBiHomogeneous`: a polynomial law `f : (M × M') →ₚ[R] N` is bihomogeneous of
  bidegree `n : ℕ × ℕ` if for all `S : Type u`, `(s : S × S)`, `m : M`, `m': M'`, one has
  `f (s.1 • m, rs.2 • m') = (s.1 ^ n.1 * s.2 ^ n.2) • f (m, m')`.
  The property extends to all `R`-algebras for `f.toFun`.

* `PolynomialLaw.biGrade n` : the submodule of bihomogeneous polynomial laws of bidegree `n`.

* `PolynomialLaw.biComponent n f`: the bihomogeneous component of bidegree `n` of a
  `PolynomialLaw` `f`.

## Main Results

* `PolynomialLaw.IsBiHomogeneous.isHomogeneous` : a bihomogeneous polynomial law is homogeneous.

* `PolynomialLaw.IsBiHomogeneous.biCoeff_eq_zero` : the bicoefficients of a bihomogeneous
  polynomial law of bidegree `n` vanish outside of bidegree `n`.

* `PolynomialLaw.lfsum_biComponent` : any polynomial law is the sum of its bihomogeneous
  components, in the following sense : for all `R`-algebras `S` and all `m : S ⊗[R] M`, the function
  `n ↦ (f.bicomponent n).toFun' S m` has finite support, and its sum is `f.toFun' S m`.

-/
noncomputable section

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R]

variable {M M' : Type v} {N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N] [Module R N]

open LinearMap TensorProduct

section BiHomogeneous

open Finsupp MvPolynomial

open TensorProduct

/--  A polynomial law `f : (M × M') →ₚ[R] N` is bihomogeneous of bidegree `n : ℕ × ℕ` if for all
  `S : Type u`, `(s : S × S)`, `m : M`, `m': M'`, one has
  `f (s.1 • m, rs.2 • m') = (s.1 ^ n.1 * s.2 ^ n.2) • f (m, m')`. -/
def IsBiHomogeneous (n : ℕ × ℕ) (f : (M × M') →ₚₗ[R] N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (s : S × S) (m : S ⊗[R] (M × M')),
    f.toFun' S (s.1 • TensorProduct.compFstRight R S S M M' m +
      s.2 • TensorProduct.compSndRight R S S M M' m) = (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun' S m

theorem IsBiHomogeneous_add (n : ℕ × ℕ) {f g : (M × M') →ₚₗ[R] N}
    (hf : f.IsBiHomogeneous n) (hg : g.IsBiHomogeneous n) :
    (f + g).IsBiHomogeneous n := fun S _ _ s m ↦ by
  simp [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsBiHomogeneous_smul (n : ℕ × ℕ) (r : R) {f : (M × M') →ₚₗ[R] N}
    (hf : f.IsBiHomogeneous n) :
    (r • f).IsBiHomogeneous n := fun S _ _ s m ↦ by
  simp [smul_def, Pi.smul_apply, hf S, smul_comm r]

/-- The submodule of bihomogeneous polynomial laws of bidegree `n`. -/
def biGrade (n : ℕ × ℕ) : Submodule R ((M × M') →ₚₗ[R] N) where
  carrier            := IsBiHomogeneous n
  add_mem' hf hg     := IsBiHomogeneous_add n hf hg
  smul_mem' r f hf   := IsBiHomogeneous_smul n r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

variable (n : ℕ × ℕ) (r : R) (f : (M × M') →ₚₗ[R] N)

lemma mem_biGrade  :
    f ∈ biGrade n ↔ IsBiHomogeneous n f := by rfl

variable {n f}

lemma isBiHomogeneous_toFun (hf : IsBiHomogeneous n f) (S : Type*) [CommSemiring S]
    [Algebra R S] (s : S × S) (m : S ⊗[R] (M × M')) :
    f.toFun S (s.1 • TensorProduct.compFstRight R S S M M' m +
      s.2 • TensorProduct.compSndRight R S S M M' m) =
      (s.1 ^ n.1 * s.2 ^ n.2) • f.toFun S m := by
  choose d ψ m' r' hm' hr1 hr2 using PolynomialLaw.exists_lift_pair m s
  simp only [← hr1, ← hm', ← hr2, ← map_pow, ← map_mul, ← isCompat_apply, toFun_eq_toFun',
    ← TensorProduct.rTensor_smul]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  simp only [compFstRight, inlRight, fstRight, coe_comp, LinearEquiv.coe_coe, coe_inl, coe_fst,
    Function.comp_apply, compSndRight, inrRight, sndRight, coe_inr, coe_snd]
  apply congr_arg
  simp only [map_add, TensorProduct.rTensor_smul]
  congr <;>
  rw [LinearEquiv.symm_apply_eq] <;>
  simp [Prod.ext_iff, prodRight_rTensor_fst_eq_rTensor_prodRight',
      LinearEquiv.apply_symm_apply, prodRight_rTensor_snd_eq_rTensor_prodRight']

/-- If `f` is bihomogeneous of bidegree `n`, then `f.ground` is too.  -/
lemma isBiHomogeneous_ground (hf : IsBiHomogeneous n f) (r : R × R) (m : (M × M')) :
    f.ground ((r.1 • m.1, r.2 • m.2)) = (r.1 ^ n.1 * r.2 ^ n.2) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (M × M')).symm m)
  simp only [lid_symm_apply] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply, ← map_smul, ← hfrm]
  congr
  simp only [prod_right_ext_iff R, map_add, fstRight_compFstRight_eq, fstRight_compSndRight_eq,
    sndRight_compFstRight_eq, sndRight_compSndRight_eq]
  simp [fstRight, sndRight]

theorem IsBiHomogeneous.comp {P : Type*} [AddCommMonoid P] [Module R P]
    (hf : f.IsBiHomogeneous n) {g : N →ₚₗ[R] P} {q : ℕ}  (hg : g.IsHomogeneous q) :
    (g.comp f).IsBiHomogeneous (q • n) := by
  intro S _ _ r m
  simp [comp_toFun', Function.comp_apply, hf S, hg S, nsmul_eq_mul, Prod.fst_mul,
    Prod.fst_natCast, Nat.cast_id, mul_comm q, pow_mul, Prod.snd_mul, Prod.snd_natCast, mul_pow]

theorem IsBiHomogeneous.isHomogeneous
    (hf : f.IsBiHomogeneous n) : f.IsHomogeneous (n.1 + n.2) := by
  intro S _ _ r m
  have hf' := hf S (r, r) m
  simp only [← pow_add] at hf'
  rw [← hf', ← smul_add]
  simp [compFstRight_add_compSndRight]

/-- The bicoefficients of a homogeneous polynomial law of bidegree `n` vanish outside of
bidegree `n`. -/
lemma isBiHomogeneous_biCoeff {d : ℕ × ℕ} (hf : IsBiHomogeneous n f) (m : M × M')
    (hd : d ≠ n) : PolynomialLaw.biCoeff m f d = 0 := by
  have hf' := isBiHomogeneous_toFun hf
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
  rw [this, h1, toFun_add_tmul_eq_biCoeff_sum, toFun_add_tmul_eq_biCoeff_sum] at hf'
  simp only [smul_sum, smul_tmul', smul_eq_mul] at hf'
  let φ : MvPolynomial (Fin 2) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R ((finTwoArrowEquiv' ℕ).symm d)))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [Fin.isValue, map_finsuppSum, one_pow, mul_one] at hφ
  rw [Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  · simp only [lcoeff, Fin.isValue, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      rTensor_tmul, LinearMap.coe_mk, AddHom.coe_mk, lid_tmul, φ, Fin.isValue,
      X_pow_mul_X_pow_eq_prod, prod_X_pow_eq_monomial', coeff_monomial, _root_.one_smul,
      ite_smul, _root_.one_smul, _root_.zero_smul,] at hφ
    simp only [↓reduceIte, EmbeddingLike.apply_eq_iff_eq, left_eq_ite_iff] at hφ
    exact hφ (by simp [(Ne.symm hd)])
  · intro k hk0 hkd
    simp only [Fin.isValue, X_pow_mul_X_pow_eq_prod, prod_X_pow_eq_monomial', coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, lcoeff_apply, coeff_monomial,
      lid_tmul, ite_smul, _root_.one_smul, _root_.zero_smul, φ]
    rw [if_neg (by simp [-finTwoArrowEquiv'_symm_apply, (Ne.symm hd)])]
  · intro k hk0 hkd
    simp only [Fin.isValue, X_pow_mul_X_pow_eq_prod, prod_X_pow_eq_monomial', coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, lcoeff_apply, coeff_monomial,
      lid_tmul, ite_smul, _root_.one_smul, _root_.zero_smul,  φ]
    rw [if_neg (by simp [-finTwoArrowEquiv'_symm_apply, hkd])]

/-- The bi-coefficients of a homogeneous polynomial law of bi-degree `n` vanish outside of
bi-degree `n`. -/
lemma isHomogeneous_biCoeff {n : ℕ} {d : ℕ × ℕ} (hf : IsHomogeneous n f)
    (m : M × M') (hd : d.1 + d.2 ≠ n) : PolynomialLaw.biCoeff m f d = 0 := by
  simp only [biCoeff_apply, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, biGenerize',
    LinearMap.coe_mk, AddHom.coe_mk,  scalarRTensor_apply, EmbeddingLike.map_eq_zero_iff]
  simp only [toFun_add_tmul_eq_coeff_sum, sum, map_sum, rTensor_tmul, lcoeff_apply]
  have h2' (e :  Fin 2 →₀ ℕ) : X (R := R) (0 : Fin 2) ^ (e 0) * X 1 ^ (e 1) =
      ∏ (i : Fin 2), X i ^ e i := by simp [Fin.prod_univ_two]
  simp_rw [h2', prod_X_pow_eq_monomial', coeff_monomial]
  simp only [ite_tmul, Finset.sum_ite_eq', Finsupp.mem_support_iff, ne_eq]
  rw [if_neg]
  simp only [Finsupp.mem_support_iff, ne_eq, not_not]
  apply isHomogeneous_coeff hf
  rw [finTwoArrowEquiv'_sum_eq]
  exact hd

lemma biCoeff_zero_of_isHomogeneous {n a b : ℕ} (hn : a + b ≠ n)
    (hf : IsHomogeneous n f) : biCoeff (0 : M × M') f (a, b) = 0 :=
  isHomogeneous_biCoeff hf 0 (by simp [hn])

theorem toFun_zero_of_constantBiCoeff_zero (hf : biCoeff (0 : M × M') f 0 = 0) (S : Type*)
    [CommSemiring S] [Algebra R S] : f.toFun S 0 = 0 := by
  have : (0 : S ⊗[R] (M × M')) = (0 : S) ⊗ₜ[R] ((0 : M), (0 : M')) := by simp
  rw [this, toFun_tmul_fst_eq_biCoeff_sum ((0 : M), (0 : M'))]
  simp only [sum]
  rw [Prod.mk_zero_zero, Finset.sum_eq_single 0]
  simp [hf]
  · intro k hk hk0
    simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero, not_and_or] at hk0
    rcases hk0 with (hk1 | hk2)
    · simp [hk1]
    · simp [hk2]
  · intro h0
    simp only [Finsupp.mem_support_iff, ne_eq, not_not] at h0
    simp [h0]

theorem toFun'_zero_of_constantBiCoeff_zero (hf : biCoeff (0 : M × M') f 0 = 0) (S : Type u)
    [CommSemiring S] [Algebra R S] : f.toFun' S 0 = 0 := by
  rw [← toFun_eq_toFun', toFun_zero_of_constantBiCoeff_zero hf]

theorem isBiHomogeneous_biCoeffBaseChangeupport_le {a b : ℕ} (hf : f.IsBiHomogeneous (a, b)) (m : M × M') :
    (biCoeff m f).support ⊆ {(a, b)} := by
  intro d hd
  by_contra hd'
  exact (Finsupp.mem_support_iff.mp hd)
    (isBiHomogeneous_biCoeff hf m (Finset.notMem_singleton.mp hd'))

theorem isBiHomogeneous_biCoeff_eq {a b : ℕ}
    (hf : f.IsBiHomogeneous (a, b)) (m : M × M') :
    (biCoeff m f) (a, b) = f.ground m := by
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : (1 : R) ⊗ₜ[R] m = (1, (1 : R)).1 ⊗ₜ[R] (m.1, 0) + ((1 : R), 1).2 ⊗ₜ[R] (0, m.2) := by
    simp [← tmul_add]
  rw [this, toFun_add_tmul_eq_biCoeff_sum, map_finsuppSum,
    sum_of_support_subset _ (isBiHomogeneous_biCoeffBaseChangeupport_le hf m) _ (by simp)]
  simp

section Components

/- Here we define the bihomogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

open MvPolynomial


variable (n f) (g : (M × M') →ₚₗ[R] N)

/-- The bihomogeneous component of bidegree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def biComponent : ((M × M') →ₚₗ[R] N) →ₗ[R] ((M × M') →ₚₗ[R] N) where
  toFun f := {
    toFun' S _ _ := fun m ↦ biCoeffBaseChange f m n
    isCompat' {S _ _} {S' _ _} φ := by
      ext sm
      apply rTensor_biCoeffBaseChange_eq }
  map_add' f g  := by
    ext S _ _ sm
    simp [biCoeffBaseChange_apply, map_add, map_add, Pi.add_apply, add_def, add_toFun_apply]
  map_smul' r f := by
    ext S _ _ sm
    simp [biCoeffBaseChange_apply, Pi.smul_apply, rTensor_apply, map_smul, smul_def, smul_toFun]

theorem biComponent.toFun'_apply (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M')) :
    (f.biComponent n).toFun' S m = biCoeffBaseChange f m n := rfl

theorem biComponent_toFun_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M')) :
    (f.biComponent n).toFun S m = biCoeffBaseChange f m n := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, biComponent.toFun'_apply]
  exact rTensor_biCoeffBaseChange_eq f n q ψ

lemma biComponent_isBiHomogeneous [Nontrivial R] : IsBiHomogeneous n (f.biComponent n) :=
  fun _ _ _ s _ ↦ biCoeffBaseChange_apply_smul f n _ s

 theorem mem_support_biComponent' {S : Type u} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (M × M')) :
    n ∈ Function.support (fun i => ((fun n => f.biComponent n) i).toFun' S m) ↔
    ((finTwoArrowEquiv' ℕ).symm n) ∈ (MvPolynomial.rTensor
      (f.toFun (MvPolynomial (Fin 2) S) ((LinearEquiv.rTensor (R := R) (M × M')
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
            (X (0 : Fin 2) ⊗ₜ[R] (compFstRight R S S M M' m) +
              X (1 : Fin 2) ⊗ₜ[R] (compSndRight R S S M M' m)))))).support
            := by
  simp [biComponent, biCoeffBaseChange_def, Fin.isValue, map_add, Function.mem_support, ne_eq,
    Finsupp.mem_support_iff]

theorem mem_support_biComponent {S : Type*} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (M × M')) :
    n ∈ Function.support (fun i => ((fun n => f.biComponent n) i).toFun S m) ↔
    ((finTwoArrowEquiv' ℕ).symm n) ∈ (MvPolynomial.rTensor
      (f.toFun (MvPolynomial (Fin 2) S) ((LinearEquiv.rTensor (R := R) (M × M')
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
            (X (0 : Fin 2) ⊗ₜ[R] (compFstRight R S S M M' m) +
              X (1 : Fin 2) ⊗ₜ[R] (compSndRight R S S M M' m)))))).support := by
  rw [Function.mem_support, ne_eq, Finsupp.mem_support_iff, not_iff_not,
    biComponent_toFun_apply, biCoeffBaseChange_def]

private lemma LocFinsupp_biComponent_aux {S : Type u} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (M × M')) : (Function.support fun n ↦
    (MvPolynomial.rTensor
        (f.toFun (MvPolynomial (Fin 2) S)
          ((LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
              (X 0 ⊗ₜ[R] (compFstRight R S S M M') m + X 1 ⊗ₜ[R] (compSndRight R S S M M') m)))))
      ((finTwoArrowEquiv' ℕ).symm n)).Finite := by
  let U := (MvPolynomial.rTensor
      (f.toFun (MvPolynomial (Fin 2) S) ((LinearEquiv.rTensor (R := R) (M × M')
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
            (X (0 : Fin 2) ⊗ₜ[R] (compFstRight R S S M M' m) +
              X (1 : Fin 2) ⊗ₜ[R] (compSndRight R S S M M' m)))))).support
  suffices hU : Finite U by
    exact Set.Finite.of_injOn (fun a ha ↦ (mem_support_biComponent' a f m).mp ha)
      (Equiv.injective (finTwoArrowEquiv' ℕ).symm).injOn hU
  exact Finset.finite_toSet _

theorem LocFinsupp_biComponent : LocFinsupp fun n ↦ f.biComponent n :=
  fun _ _ _ m ↦ LocFinsupp_biComponent_aux f m

 theorem LocFinsupp_biComponent_eq {S : Type u} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (M × M')) :
    (Finsupp.ofSupportFinite (fun i ↦ (f.biComponent i).toFun' S m)
      (LocFinsupp_biComponent f S m)) =
    Finsupp.ofSupportFinite (fun n ↦ MvPolynomial.rTensor
      (f.toFun (MvPolynomial (Fin 2) S) ((LinearEquiv.rTensor (R := R) (M × M')
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
            (X (0 : Fin 2) ⊗ₜ[R] (compFstRight R S S M M' m) +
              X (1 : Fin 2) ⊗ₜ[R] (compSndRight R S S M M' m)))))
              ((finTwoArrowEquiv' ℕ).symm n)) (LocFinsupp_biComponent_aux f m) := by
  ext n
  simp [biComponent, biCoeffBaseChange_apply, Finsupp.ofSupportFinite_coe]

open Finsupp

theorem tmul_eq_aeval_sum' (S : Type*) [CommSemiring S] [Algebra R S] (s : S) (m : M × M') :
    s ⊗ₜ[R] m =
      (aeval 1) (scalarRTensorAlgEquiv (X (0 : Fin 2) ⊗ₜ[R] s)) ⊗ₜ[R] (m.1, (0 : M')) +
      (aeval 1) (scalarRTensorAlgEquiv (X (1 : Fin 2) ⊗ₜ[R] s)) ⊗ₜ[R] ((0 : M), m.2) := by
  have hm : m = (m.1, 0) + (0, m.2) := by rw [Prod.fst_add_snd]
  by_cases hR : Nontrivial R
  · conv_lhs => rw [hm, tmul_add]
    congr
    all_goals
      simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
        mapAlgEquiv_apply, rTensorAlgHom_apply_eq, aeval_def, Algebra.algebraMap_self, eval₂_map,
        RingHomCompTriple.comp_eq]
      rw [MvPolynomial.rTensor_apply_tmul, Finsupp.sum]
      simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
      rw [finsupp_support_eq_support, support_X (R := R)]
      simp only [Finset.sum_singleton, map_zero, Finsupp.prod_single_index, mul_one,
        Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]
      simp [X, ← single_eq_monomial, single_eq_same]
  · have hSM := TensorProduct.not_nontrivial_of_not_nontrivial R S (M × M')
      (Algebra.not_nontrivial_of_not_nontrivial R S hR)
    simp only [nontrivial_iff, ne_eq, not_exists, not_not] at hSM
    apply hSM

theorem recompose_biComponent :
    PolynomialLaw.lfsum (fun n ↦ f.biComponent n) = f := by
  ext S _ _ sm
  rw [lfsum_toFun'_eq_of_locFinsupp (LocFinsupp_biComponent f), LocFinsupp_biComponent_eq]
  have hsm' : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor (M × M') (
    (LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
        (X (0 : Fin 2) ⊗ₜ[R] TensorProduct.compFstRight R S S M M' sm +
          X (1 : Fin 2) ⊗ₜ[R] TensorProduct.compSndRight R S S M M' sm))) := by
    simp only [LinearMap.rTensor]
    induction sm using TensorProduct.induction_on with
    | zero =>  simp [map_zero, tmul_zero]
    | tmul s m =>
      simp only [Fin.isValue, compFstRight_tmul, inlRight_tmul, compSndRight_tmul, inrRight_tmul,
        map_add, assoc_symm_tmul, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_tmul,
        AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', id_coe, id_eq]
      rw [tmul_eq_aeval_sum']
    | add sm₁ sm₂ hsm₁ hsm₂ =>
      simp only [Fin.isValue, map_add, tmul_add] at hsm₁ hsm₂ ⊢
      rw [add_add_add_comm, ← hsm₁, ← hsm₂]
  conv_rhs => rw [← toFun_eq_toFun', hsm', ← f.isCompat_apply]
  set tk := (f.toFun (MvPolynomial (Fin 2) S)
    ((LinearEquiv.rTensor (R := R) (M × M') scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial (Fin 2) R) S (M × M')).symm
        (X 0 ⊗ₜ[R] (compFstRight R S S M M') sm + X 1 ⊗ₜ[R] (compSndRight R S S M M') sm))))
          with htk
  simp_rw [← htk]
  convert rTensor'_sum (A := R) (fun _ ↦ 1) tk
  · simp only [_root_.one_smul]
    exact Finset.sum_bij (fun a _ ↦ (finTwoArrowEquiv' ℕ).symm a) (fun _ ha ↦ by simpa using ha)
      (fun _ _ _ _ h ↦ by simpa [-finTwoArrowEquiv'_symm_apply] using h)
      (fun a ha ↦ ⟨finTwoArrowEquiv' ℕ a, by simpa only [Finsupp.mem_support_iff,
        ofSupportFinite_coe, Equiv.symm_apply_apply, ne_eq] using ha, Equiv.symm_apply_apply _ _⟩)
      (fun _ _ ↦ by rw [ofSupportFinite_coe])
  · ext p
    simp [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', aeval_eq_eval₂Hom, eval_eq,
      Finset.prod_const_one, MvPolynomial.lsum, coe_restrictScalars, LinearMap.coe_mk,
      AddHom.coe_mk, Finsupp.sum, MvPolynomial.coeff, finsupp_support_eq_support]

end Components

end BiHomogeneous

/- # Bihomogeneous components of a polynomial map

-/


variable {M M' : Type v} {N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [AddCommMonoid N] [Module R N]

open LinearMap TensorProduct

section BiHomogeneous

open Finsupp MvPolynomial

open TensorProduct


variable (n : ℕ × ℕ) (f : (M × M') →ₚₗ[R] N)


variable {n f}



section Components

open MvPolynomial

variable (S : Type*) [CommSemiring S] [Algebra R S]

variable (R M M')


/-- The bi-coefficients of a bihomogeneous polynomial map of bi-degree `n` vanish outside of
bi-degree `n`. -/
lemma IsBiHomogeneous_biCoeffBaseChange {d : ℕ × ℕ} (hf : IsBiHomogeneous n f)
    (sm : S ⊗[R] (M × M')) (hd : d ≠ n) : biCoeffBaseChange f sm d = 0 := by


  sorry

/-- The bi-coefficients of a homogeneous polynomial map of degree `n` vanish outside of
bi-degree `n`. -/
lemma IsHomogeneous_biCoeffBaseChange {n : ℕ} {d : ℕ × ℕ} (hf : IsHomogeneous n f)
    (sm : S ⊗[R] (M × M')) (hd : d.1 + d.2 ≠ n) : biCoeffBaseChange f sm d = 0 := by

  sorry

/-- The bi-coefficients of a homogeneous polynomial map of bi-degree `n` vanish outside of
bi-degree `n`. -/
lemma IsHomogeneous_biCoeffBaseChange' {n : ℕ} {d : ℕ × ℕ} (hf : IsHomogeneous n f)
    (sm : S ⊗[R] (M × M')) (hd : d.1 + d.2 ≠ n) : biCoeffBaseChange f sm d = 0 := by
  induction sm using TensorProduct.induction_on with
  | zero =>
      simp only [biCoeffBaseChange_apply, Fin.isValue, map_zero, tmul_zero, add_zero,
      finTwoArrowEquiv'_symm_apply]

      sorry
    /- have h0 : f.toFun (MvPolynomial (Fin 2) S) 0 = 0 := by
      apply toFun_zero_of_constantBiCoeff_zero
      apply biCoeff_zero_of_IsHomogeneous _ hf
      sorry -- **MI** : this seems to suggest n ≠ 0 is required (?) -/
    /- simp only [biCoeffBaseChange_apply, Fin.isValue, map_zero, tmul_zero, add_zero, h0,
      finTwoArrowEquiv'_symm_apply, coe_zero, Pi.zero_apply] -/
  | add sm sm' hsm hsm' =>
    -- **MI** : unclear
    sorry
  | tmul s m =>
    have hsm : s ⊗ₜ m = ((prodRight R R S M M').symm (s ⊗ₜ[R] m.1, s ⊗ₜ[R] m.2)) := by simp
    have ha (a : ℕ × ℕ) : ((C s * X (0 : Fin 2)) ^ a.1 * (C s * X 1) ^ a.2) =
        C (s ^ (a.1 + a.2)) * (X 0 ^ a.1 * X 1 ^ a.2) := by
      simp only [Fin.isValue, mul_pow, pow_add, C_mul, C_pow]
      ring
    simp_rw [hsm, biCoeffBaseChange_apply]
    sorry
    /-simp only [Fin.isValue, map_finsuppSum, Finsupp.sum_apply,
      rTensor_apply, rTensor_tmul, coe_restrictScalars, lcoeff_apply]
     rw [Finsupp.sum]
    simp_rw [ha, coeff_C_mul, X_pow_mul_X_pow_eq_prod, prod_X_pow_eq_monomial', coeff_monomial]
    simp only [mul_ite, mul_one, mul_zero, ite_tmul, Finset.sum_ite,
      Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single d]
    simp [IsHomogeneous_biCoeff hf _ hd]
    · intro b hb hb'
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq,
        EmbeddingLike.apply_eq_iff_eq] at hb
      exact absurd hb.2 hb'
    · intro hd
      simp only [finTwoArrowEquiv'_symm_apply, Finset.mem_filter, Finsupp.mem_support_iff, ne_eq,
        and_true, not_not] at hd
      simp [hd] -/

variable (n f)


end Components

end BiHomogeneous
