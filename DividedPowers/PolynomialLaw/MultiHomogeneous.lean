/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.PolynomialLaw.Homogeneous
import DividedPowers.PolynomialLaw.MultiCoeff
import Mathlib.Data.Finsupp.Weight

universe u uι

/- # Multihomogeneous components of a polynomial law

Let `R` be a commutative ring, let `M` and `N` be `R`-modules, and let `f : M →ₚₗ[R] N` be a
polynomial law.

## Main Definitions

* `PolynomialLaw.IsMultiHomogeneous`: a polynomial law `f : Π (i : ι), M i →ₚ[R] N` is
  multihomogeneous of multidegree `n : ι →₀ ℕ` if for all `S : Type u` and all families
  `{z_i : S ⊗ M i}_{i : ι}`, `{r_i : S}_{i : ι}`, one has
  `f (r_1 • z_1, r_2 • z_2, ...) = Π i r_i^(n i) • f (z_1, z_2, ...)`.
  The property extends to all `R`-algebras for `f.toFun`.

* `PolynomialLaw.multiGrade n` : the submodule of multihomogeneous polynomial laws of
  multidegree `n`.

* `PolynomialLaw.multiComponent n f`: the multihomogeneous component of multidegree `n` of a
  `PolynomialLaw` `f`.

## Main Results

* `PolynomialLaw.IsMultiHomogeneous.isHomogeneous` : a multihomogeneous polynomial law is
  homogeneous.

* `PolynomialLaw.IsMultiHomogeneous.multiCoeff_eq_zero` : the multicoefficients of a
  multihomogeneous polynomial law of multidegree `n` vanish outside of multidegree `n`.

*  `PolynomialLaw. IsMultiHomogeneous.comp`: composition of multihomogeneous polynomial laws.

* `PolynomialLaw.lfsum_multiComponent` : any polynomial law is the sum of its multihomogeneous
  components, in the following sense : for all `R`-algebras `S` and all `m : S ⊗[R] M`, the function
  `n ↦ (f.multicomponent n).toFun' S m` has finite support, and its sum is `f.toFun' S m`.

-/

open LinearMap TensorProduct

noncomputable section

namespace PolynomialLaw

section MultiHomogeneous

section

open Finsupp MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {N : Type*} [AddCommMonoid N] [Module R N]
  (n : ι →₀ ℕ) (r : R) (f g : (Π i, M i) →ₚₗ[R] N)

/-- A polynomial law `f : Π (i : ι), M i →ₚ[R] N` is multihomogeneous of multidegree `n : ι →₀ ℕ`
  if for all `S : Type u`, all families `{z_i : S ⊗ M i}_{i : ι}`, `{r_i : S}_{i : ι}`, one has
  `f (r_1 • z_1, r_2 • z_2, ...) = Π i r_i^(n i) • f (z_1, z_2, ...)`. -/
def IsMultiHomogeneous : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : ι → S) (m : S ⊗ ((i : ι) → M i)),
    f.toFun' S (∑ i, r i • compRight R S S M i m) =
      (∏ i, r i ^ n i) • f.toFun' S m

variable {f g}

theorem IsMultiHomogeneous_add (hf : f.IsMultiHomogeneous n)
    (hg : g.IsMultiHomogeneous n) : (f + g).IsMultiHomogeneous n :=
  fun S _ _ s m ↦ by simp [-piRight_apply, add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsMultiHomogeneous_smul (hf : f.IsMultiHomogeneous n) :
    (r • f).IsMultiHomogeneous n := fun S _ _ s m ↦ by
  simp [smul_def, Pi.smul_apply, hf S, smul_comm r]

-- Prop. I.3
/-- The submodule of multihomogeneous polynomial laws of multidegree `n`. -/
def multiGrade : Submodule R ((Π i, M i) →ₚₗ[R] N) where
  carrier            := IsMultiHomogeneous n
  add_mem' hf hg     := IsMultiHomogeneous_add n hf hg
  smul_mem' r f hf   := IsMultiHomogeneous_smul n r hf
  zero_mem' S _ _ r  := by simp [zero_def, smul_zero]

lemma mem_multiGrade : f ∈ multiGrade n ↔ IsMultiHomogeneous n f := by rfl

variable {n}

/-- If `f` is multihomogeneous of multidegree `n`, then all `f.toFun S` are multihomogeneous of
  multidegree `n`. -/
lemma IsMultiHomogeneous.toFun (hf : IsMultiHomogeneous n f) (S : Type*)
    [CommSemiring S] [Algebra R S] (r : ι → S) (m : S ⊗[R] (Π i, M i)) :
    f.toFun S (∑ i, r i • compRight R S S M i m) = (∏ i, (r i)^(n i)) • f.toFun S m := by
  choose d ψ m' r' hm' hr' using PolynomialLaw.exists_lift'' m r
  simp only [← hr', ← hm', ← map_pow, ← map_prod, ← isCompat_apply, toFun_eq_toFun',
    ← TensorProduct.rTensor_smul]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  simp only [TensorProduct.compRight, singleRight, projRight, coe_comp, LinearEquiv.coe_coe,
    coe_single, coe_proj, Function.comp_apply, Function.eval]
  simp only [map_sum, TensorProduct.rTensor_smul]
  congr
  ext i
  congr
  rw [LinearEquiv.symm_apply_eq]
  ext j
  by_cases hij : j = i
  · subst hij
    simp [piRight_rTensor_eq_rTensor_piRight']
  · simp [piRight_rTensor_eq_rTensor_piRight', hij]

/-- If `f` is multihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isMultiHomogeneous_ground (hf : IsMultiHomogeneous n f) (r : ι → R)
    (m : (Π i, M i)) : f.ground (r • m) = (∏ i, (r i)^(n i)) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (Π i, M i)).symm m)
  simp only [lid_symm_apply] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply, ← map_smul, ← hfrm]
  congr
  rw [right_ext_iff R]
  intro i
  simp_rw [map_sum, projRight_compRight]
  simp [projRight]

theorem eq_sum_single_comp_proj (f : N  →ₚₗ[R] (Π i, M i)) :
    f = ∑ (i : ι), ((single R M i).comp (proj i)).toPolynomialLaw.comp f := by
  rw [← sum_comp]
  convert f.id_comp.symm
  simp only [← toDegreeOnePolynomialLaw_apply, ← Submodule.coe_sum,
    ← map_sum]
  suffices ∑ x, LinearMap.single R M x ∘ₗ proj x = LinearMap.id by
    rw [this]
    rw [toDegreeOnePolynomialLaw_apply, toPolynomialLaw_id]
  aesop

theorem toFun_eq_sum_single_proj (f : N  →ₚₗ[R] (Π i, M i)) {S : Type*} [CommSemiring S]
    [Algebra R S] (n : S ⊗[R] N) : f.toFun S n =
      ∑ (i : ι), singleRight R S S M i (((proj i).toPolynomialLaw.comp f).toFun S n) := by
  nth_rewrite 1 [eq_sum_single_comp_proj f]
  rw [sum_toFun]
  apply Finset.sum_congr rfl
  intro i _
  simp only [toPolynomialLaw_comp, comp_toFun, toPolynomialLaw_toFun, Function.comp_apply]
  congr
  ext m
  simp [singleRight_tmul]

/-- Composition of multihomogeneous polynomial laws.

See `IsMultiHomogeneous.comp` for a generalization where the target module is a product. -/
theorem IsMultiHomogeneous.comp' {P : Type*} [AddCommMonoid P] [Module R P]
    {g : N →ₚₗ[R] P} {p : ι →₀ ℕ} {q : ℕ} (hf : f.IsMultiHomogeneous p)
    (hg : g.IsHomogeneous q) : (g.comp f).IsMultiHomogeneous (q • p) := by
  intro S _ _ r m
  simp [comp_toFun', mul_comm q, pow_mul, Finset.prod_pow, hf S, hg S]

/-- Composition of multihomogeneous polynomial laws, [Roby-1963], I.2.

When the target module is not in product form, use `IsMultiHomogeneous.comp'. -/
theorem IsMultiHomogeneous.comp {κ : Type*} [Fintype κ] [DecidableEq κ] {N : κ → Type*}
    [∀ k, AddCommMonoid (N k)] [∀ k, Module R (N k)] {P : Type*} [AddCommMonoid P] [Module R P]
    {f : (Π i, M i) →ₚₗ[R] (Π k, N k)} {g : (Π k, N k) →ₚₗ[R] P}{n : κ → ι →₀ ℕ}
    (hf : ∀ k, IsMultiHomogeneous (n k) ((proj k).toPolynomialLaw.comp f)) {p : κ →₀ ℕ}
    (hg : IsMultiHomogeneous p g) {q : ι →₀ ℕ} (hq : ∀ i, q i = ∑ k, n k i * p k) :
    IsMultiHomogeneous q (g.comp f) := by
  intro S _ _ s m
  simp only [← toFun_eq_toFun', comp_toFun, Function.comp_apply]
  nth_rewrite 1 [f.toFun_eq_sum_single_proj]
  simp_rw [(hf _).toFun, map_smul]
  simp only [comp_toFun, Function.comp_apply, toPolynomialLaw_toFun]
  set r := fun x ↦ ∏ i, s i ^ (n x) i with hr
  change g.toFun S (∑ x, (r x • _)) = _
  generalize f.toFun S m = m'
  specialize hg S (fun x ↦ r x)
  rw [← toFun_eq_toFun'] at hg
  convert hg m' with i
  · simp only [TensorProduct.compRight, coe_comp, Function.comp_apply]
    congr
    ext; simp [projRight]
  · simp only [hr]
    simp_rw [← Finset.prod_pow, ← pow_mul]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_pow_eq_pow_sum, hq]

/-- A multihomogeneous polynomial law is homogeneous. -/
theorem IsMultiHomogeneous.isHomogeneous (hf : f.IsMultiHomogeneous n) :
    f.IsHomogeneous n.degree := by
  intro S _ _ r m
  rw [degree_eq_sum, ← Finset.prod_pow_eq_pow_sum, ← hf S (fun i ↦ r) m, ← Pi.smul_def]
  simp [Pi.smul_apply, ← Finset.smul_sum, sum_compRight]

/-- The multicoefficients of a multihomogeneous polynomial law of multidegree `n` vanish outside of
  multidegree `p`. -/
lemma IsMultiHomogeneous.multiCoeff_eq_zero {n d : ι →₀ ℕ}
    (hf : IsMultiHomogeneous n f) (m : Π i, M i) (hd : d ≠ n) :
    PolynomialLaw.multiCoeff m f d = 0 := by
  have hf' := hf.toFun (MvPolynomial ι R) X (∑ i, 1 ⊗ₜ[R] Pi.single i (m i))
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
  let hφ := LinearMap.congr_arg (f := φ)  hf'
  simp only [mul_one, map_finsuppSum, one_pow, Finset.prod_const_one] at hφ
  rw [Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d ?_ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  · rw [ne_comm] at hd
    revert hd
    simpa [φ, prod_X_pow_eq_monomial'] using hφ
  · intro k hk0 hkd
    simp [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, lcoeff_apply, φ,
      prod_X_pow_eq_monomial', coeff_monomial, if_neg (Ne.symm hd)]
  · intro k hk0 hkd
    simp [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, lcoeff_apply, φ,
      prod_X_pow_eq_monomial', coeff_monomial, if_neg hkd]

theorem isMultiHomogeneousOne_multiCoeff {i : ι}
    (hf : f.IsMultiHomogeneous (Finsupp.single i 1)) (m : Π i, M i) {d : ι →₀ ℕ}
    (hd : d ≠ Finsupp.single i 1) : (multiCoeff m f) d = 0 :=
  hf.multiCoeff_eq_zero m hd

theorem isMultiHomogeneousOne_multiCoeff_support_le {i : ι}
    (hf : f.IsMultiHomogeneous (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f).support ⊆ Finset.map
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [Finsupp.mem_support_iff, ne_eq] at hd
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and]
  exact ⟨i, ((not_imp_comm.mp (hf.multiCoeff_eq_zero m)) hd).symm⟩

theorem IsMultiHomogeneous.multicoeff_single_eq_ground {i : ι}
    (hf : f.IsMultiHomogeneous (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f) (Finsupp.single i 1) = f.ground (Pi.single i (m i)) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  have : Finset.sum Finset.univ (fun (j : ι) ↦ (Pi.single i (1 : R) j) ⊗ₜ[R] Pi.single j (m j)) =
      1 ⊗ₜ[R] Pi.single i (m i) := by
    rw [Finset.sum_eq_single i (fun _ _ hb ↦ by rw [Pi.single_eq_of_ne hb, zero_tmul])
      (fun hi => by simp [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same]
  simp only [← this, toFun_sum_tmul_eq_multiCoeff_sum, map_finsuppSum, lid_tmul]
  rw [sum_of_support_subset _ (isMultiHomogeneousOne_multiCoeff_support_le hf m) _
    (by simp), Finset.sum_map, Function.Embedding.coeFn_mk, Finset.sum_eq_single i _ (by simp)]
  · rw [Finset.prod_eq_single i (fun j _ hj => by rw [single_eq_of_ne hj, pow_zero])
      (fun hi => by simp only [Finset.mem_univ, not_true_eq_false] at hi), Pi.single_eq_same,
      one_pow, _root_.one_smul]
  · intro j _ hj
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_univ _)
      (by simp only [single_eq_same, pow_one, Pi.single_eq_of_ne hj]),
      _root_.zero_smul]

end

section Components

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R] {M : ι → Type*}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {N : Type*} [AddCommMonoid N] [Module R N]
  {S : Type*} [CommSemiring S] [Algebra R S] (n : ι →₀ ℕ)  (r : R) (f : (Π i, M i) →ₚₗ[R] N)
  (s : Π (_ : ι), S) (m : Π i, M i)

open MvPolynomial Module

/- Here we define the multihomogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

/-- The multihomogeneous component of multidegree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def multiComponent :
    ((Π i, M i) →ₚₗ[R] N) →ₗ[R] (Π i, M i) →ₚₗ[R] N where
  toFun f := {
    toFun' S _ _ := fun m ↦ multiCoeffBaseChange f m n
    isCompat' {S _ _} {S' _ _} φ := by
      ext sm
      apply rTensor_multiCoeffBaseChange_eq }
  map_add' f g := by
    ext S _ _ sm
    simp [multiCoeffBaseChange_apply, map_sum, add_toFun_apply, map_add,
      Finsupp.coe_add, Pi.add_apply, add_def]
  map_smul' r f := by
    ext S _ _ sm
    simp [multiCoeffBaseChange_apply, map_sum, smul_toFun, Pi.smul_apply,
      rTensor_apply, map_smul, smul_def]

theorem multiComponent.toFun'_apply (S : Type u) [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) : (f.multiComponent n).toFun' S m = multiCoeffBaseChange f m n := rfl

theorem multiComponent_toFun_apply (m : S ⊗[R] (Π i, M i)) :
    (f.multiComponent n).toFun S m = multiCoeffBaseChange f m n := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, multiComponent.toFun'_apply]
  exact rTensor_multiCoeffBaseChange_eq f n q ψ

lemma multiComponentIsMultiHomogeneous [Nontrivial R]  :
    IsMultiHomogeneous n (multiComponent n f) :=
  fun _ _ _ s sm ↦ multiCoeffBaseChange_apply_smul f n sm s

 theorem support_multiComponent_toFun' {S : Type u} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun' S m) =
      (MvPolynomial.rTensor (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor (R := R)
        (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv) ((TensorProduct.assoc R (MvPolynomial ι R)
          S ((i : ι) → M i)).symm (X x ⊗ₜ[R] (compRight R S S M x m)))))).support := by
  ext n
  simp [multiComponent, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, multiCoeffBaseChange_def]

theorem support_multiComponent_toFun {S : Type*} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun S m) =
      (MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
        (∑ x, (LinearEquiv.rTensor (R := R) (Π i, M i)
          scalarRTensorAlgEquiv.toLinearEquiv) ((TensorProduct.assoc R (MvPolynomial ι R) S
            ((i : ι) → M i)).symm (X x ⊗ₜ[R] (compRight R S S M x m)))))).support := by
  ext i
  rw [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_iff_not,
    multiComponent_toFun_apply, multiCoeffBaseChange_def]

theorem LocFinsupp_multiComponent : LocFinsupp (fun n ↦ f.multiComponent n) := fun S _ _ m ↦ by
  rw [support_multiComponent_toFun']
  exact Finset.finite_toSet _

 theorem LocFinsupp_multiComponent_eq {S : Type u} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    (Finsupp.ofSupportFinite (fun i => (multiComponent i f).toFun' S m)
      (LocFinsupp_multiComponent f S m)) =
        MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
          (∑ x, (LinearEquiv.rTensor (R := R) (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S
              ((i : ι) → M i)).symm (X x ⊗ₜ[R] (compRight R S S M x m))))) := by
  ext n
  simp [multiComponent, multiCoeffBaseChange_apply,  map_sum, Finsupp.ofSupportFinite_coe]

/-- A polynomial law is the locally finite sum of its multihomogeneous components. -/
theorem lfsum_multiComponent : lfsum (fun n ↦ f.multiComponent n) = f := by
  ext S _ _ sm
  rw [lfsum_toFun'_eq_of_locFinsupp (LocFinsupp_multiComponent f), LocFinsupp_multiComponent_eq]
  have hsm' : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor (Π i, M i) (∑ x,
    (LinearEquiv.rTensor (R := R) (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X x ⊗ₜ[R] compRight R S S M x sm))) := eq_rTensor_sum sm
  conv_rhs => rw [← toFun_eq_toFun', hsm', ← f.isCompat_apply]
  generalize f.toFun (MvPolynomial ι S)
    (∑ x, (LinearEquiv.rTensor (R := R) (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X x ⊗ₜ[R] compRight R S S M x sm))) = sn
  convert rTensor'_sum (A := R) (fun _ ↦ 1) sn
  · simp [_root_.one_smul]
  · ext p
    simp [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', aeval_eq_eval₂Hom, eval_eq,
      Finset.prod_const_one, MvPolynomial.lsum, coe_restrictScalars, LinearMap.coe_mk,
      AddHom.coe_mk, Finsupp.sum, MvPolynomial.coeff, finsupp_support_eq_support]

end Components

end MultiHomogeneous

end PolynomialLaw
