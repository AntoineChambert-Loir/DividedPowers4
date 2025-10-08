/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.Exponential
import DividedPowers.DPAlgebra.Graded.Basic
import DividedPowers.ForMathlib.RingTheory.TensorProduct.Basic

/-! # Base change properties of the divided power algebra

The main result of this file is the construction of a base change isomorphism
for the divided power algebra [Roby1963, theorem III.3]:
`S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M)`

## Main definitions

* `DividedPowerAlgebra.dpScalarExtensionEquiv`: the base change isomorphism
  `S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M)`
  for the divided power algebra [Roby1963, theorem III.3]

## Main results

* `DividedPowerAlgebra.dpScalarExtension_apply` and `DividedPowerAlgebra.dpScalarExtensionInv_apply`
  compute the action of `dpScalarExtensionEquiv` on basic elements in both directions.

## Note on the proof

The existence of the base change morphism is relatively straightforward, but the existence of the
morphism in the other direction is nontrivial. As in [Roby1963], the proof relies on the
`ExponentialModule` that allows to linearize the divided power algebra, and then we apply the
standard base change adjunction for linear maps.

## TODO:

* Add IsHomogeneous for maps of graded algebras/modules.

* Add GradedAlgebra instance on the base change.

-/
universe u

open AlgHom TensorProduct

namespace DividedPowerAlgebra

open Algebra.TensorProduct DividedPowers DividedPowerAlgebra

/-- A base change morphism for the divided power algebra [Roby1963, Proposition III.4].
-- TODO : prove uniqueness. -/
noncomputable def dpScalarExtension' (R : Type u) [CommSemiring R] (S : Type _) [CommSemiring S]
    [Algebra R S] (M : Type _) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] :
    S ⊗[R] DividedPowerAlgebra R M →ₐ[S] DividedPowerAlgebra S M := by
  apply AlgHom.baseChange
  apply lift' (f := fun nm => dp S nm.1 nm.2)
  · intro m; rw [dp_zero]
  · intro n r m
    rw [← algebraMap_smul S r m, dp_smul S (algebraMap R S r) n m, ← map_pow, algebraMap_smul]
  · intro n p m; rw [dp_mul]
  · intro n x y; rw [dp_add]

section dpScalarExtension

variable (A : Type*) [CommSemiring A] (R : Type*) [CommSemiring R] [Algebra A R]
    (M : Type*) [AddCommMonoid M] [Module A M]

/-- The natural `R`-algebra map from `R ⊗[A] DividedPowerAlgebra A M` to
  `DividedPowerAlgebra R (R ⊗[A] M)`. -/
noncomputable def dpScalarExtension :
    R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M) := by
  apply AlgHom.baseChange
  apply lift' (f := (fun nm => dp R nm.1 (1 ⊗ₜ[A] nm.2) : ℕ × M → DividedPowerAlgebra R (R ⊗[A] M)))
    (fun _ => by simp only [dp_zero])
  · intro n a m; simp only [tmul_smul]
    rw [← algebraMap_smul R a, dp_smul, ← map_pow, algebraMap_smul R]
  · intro n p m; rw [dp_mul]
  · intro n x y; rw [tmul_add, dp_add]

theorem dpScalarExtension_apply_dp (r : R) (n : ℕ) (m : M) :
    dpScalarExtension A R M ((r ^ n) ⊗ₜ[A] (dp A n m)) = dp R n (r ⊗ₜ[A] m) := by
  rw [dpScalarExtension, AlgHom.baseChange_tmul, lift'_apply_dp, ← dp_smul, smul_tmul',
    smul_eq_mul, mul_one]

theorem dpScalarExtension_apply_one_dp (n : ℕ) (m : M) :
    dpScalarExtension A R M (1 ⊗ₜ[A] (dp A n m)) = dp R n (1 ⊗ₜ[A] m) := by
  rw [← one_pow n, dpScalarExtension_apply_dp, one_pow]

theorem dpScalarExtension_tmul (r : R) (m : DividedPowerAlgebra A M) :
    (dpScalarExtension A R M) (r ⊗ₜ[A] m) = r • (dpScalarExtension A R M) (1 ⊗ₜ[A] m) := by
  simp only [dpScalarExtension, AlgHom.baseChange_tmul, one_smul]

/-- Uniqueness for [Roby1963, Theorem III.2] (opposite map) -/
theorem dpScalarExtension_unique
    {φ : R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M)}
    (hφ : ∀ (n : ℕ) (m : M), φ (1 ⊗ₜ[A] (dp A n m)) = dp R n (1 ⊗ₜ[A] m)) :
    φ = dpScalarExtension A R M := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x =>
    induction x using DividedPowerAlgebra.induction_on with
    | h_C a =>
      rw [mk_C, Algebra.algebraMap_eq_smul_one, tmul_smul, smul_tmul', ← mul_one s, ← smul_eq_mul,
        ← smul_assoc, ← smul_tmul', map_smul,map_smul, ← Algebra.TensorProduct.one_def,
        _root_.map_one, _root_.map_one]
    | h_add f g hf hg => simp only [tmul_add, map_add, hf, hg]
    | h_dp f n m hf =>
        rw [← mul_one s, ← tmul_mul_tmul, _root_.map_mul, _root_.map_mul, hf, hφ n m,
          dpScalarExtension_apply_one_dp]
  | add x y hx hy => simp only [map_add, hx, hy]

end dpScalarExtension

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M]

open PowerSeries

/-- The natural `S`-linear map from `S ⊗[R] M` to
  `ExponentialModule (S ⊗[R] DividedPowerAlgebra R M)`. -/
noncomputable def dpScalarExtensionExp :
    S ⊗[R] M →ₗ[S] ExponentialModule (S ⊗[R] DividedPowerAlgebra R M) :=
  (LinearMap.baseChangeEquiv R S M (ExponentialModule (S ⊗[R] DividedPowerAlgebra R M))).symm
    ((ExponentialModule.linearMap Algebra.TensorProduct.includeRight).comp (exp_LinearMap R M))

/-- The natural `S`-algebra map from `DividedPowerAlgebra S (S ⊗[R] M)` to
  `S ⊗[R] DividedPowerAlgebra R M`. -/
noncomputable def dpScalarExtensionInv  :
    DividedPowerAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] DividedPowerAlgebra R M :=
  (exponentialModule_equiv S (S ⊗[R] M)
    (S ⊗[R] DividedPowerAlgebra R M)).symm (dpScalarExtensionExp R S M)

/-- Roby1963, theorem III.2 -/
theorem dpScalarExtensionInv_apply_dp (n : ℕ) (s : S) (m : M) :
    dpScalarExtensionInv R S M (dp S n (s ⊗ₜ[R] m)) = (s ^ n) ⊗ₜ[R] (dp R n m) := by
  rw [dpScalarExtensionInv, exponentialModule_equiv_symm_apply]
  simp only [dpScalarExtensionExp, LinearMap.baseChangeEquiv, LinearEquiv.coe_symm_mk,
    AlgebraTensorModule.lift_apply, lift.tmul, LinearMap.coe_restrictScalars, LinearMap.flip_apply,
    LinearMap.lsmul_apply, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [ExponentialModule.coe_smul, PowerSeries.coeff_rescale, ExponentialModule.coeff_linearMap]
  simp [coeff_exp_LinearMap]

/-- Uniqueness claim of Roby1963, theorem III.2 -/
theorem dpScalarExtensionInv_unique
  {φ :  DividedPowerAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] DividedPowerAlgebra R M}
  (hφ : ∀ (n : ℕ) (s : S) (m : M), φ (dp S n (s ⊗ₜ[R] m)) = (s ^ n) ⊗ₜ[R] (dp R n m)) :
    φ = dpScalarExtensionInv R S M  := by
  apply AlgHom.ext
  intro x
  induction x using DividedPowerAlgebra.induction_on with
  | h_C a =>
    rw [mk_C, Algebra.algebraMap_eq_smul_one, map_smul, _root_.map_one, map_smul, _root_.map_one]
  | h_add f g hf hg => simp only [map_add, hf, hg]
  | h_dp f n sm hf =>
    suffices h_eq : φ (dp S n sm) = (dpScalarExtensionInv R S M) (dp S n sm) by
      rw [_root_.map_mul, _root_.map_mul, hf, h_eq]
    induction sm using TensorProduct.induction_on generalizing n with
    | zero =>
      rw [dp_null]
      split_ifs
      · simp only [_root_.map_one]
      · simp only [_root_.map_zero]
    | tmul s m => rw [hφ, dpScalarExtensionInv_apply_dp]
    | add x y hx hy =>
      simp only [dp_add, map_sum, _root_.map_mul]
      apply Finset.sum_congr rfl
      intro nn _hnn
      rw [hx nn.1, hy nn.2]

noncomputable example (R : Type*) [CommSemiring R] (A : Type*) [CommSemiring A] [Algebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] : Algebra S (S ⊗[R] A) := inferInstance

/-- The base change isomorphism for the divided power algebra
[Roby1963, theorem III.3] -/
noncomputable def dpScalarExtensionEquiv :
    S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom (dpScalarExtension R S M) (dpScalarExtensionInv R S M)
    (by
      apply DividedPowerAlgebra.algHom_ext
      rintro n sm
      simp only [coe_comp, Function.comp_apply, coe_id, id_eq]
      induction sm using TensorProduct.induction_on generalizing n with
      | zero =>
        rw [dp_null]
        split_ifs
        · simp only [_root_.map_one]
        · simp only [map_zero]
      | tmul s m =>
        rw [dpScalarExtensionInv_apply_dp, dpScalarExtension_apply_dp]
      | add x y hx hy =>
        rw [dp_add, map_sum, map_sum]
        apply Finset.sum_congr rfl
        rintro ⟨k, l⟩ _
        rw [_root_.map_mul, _root_.map_mul, hx, hy])
    (by
      apply Algebra.TensorProduct.ext
      · ext
      · apply DividedPowerAlgebra.algHom_ext
        intro n m
        simp only [coe_comp, coe_restrictScalars', Function.comp_apply, includeRight_apply,
          coe_id, id_eq]
        rw [← one_pow n, dpScalarExtension_apply_dp, dpScalarExtensionInv_apply_dp])

theorem coe_dpScalarExtensionEquiv :
    ⇑(dpScalarExtensionEquiv R S M) = ⇑(dpScalarExtension R S M) := by
  rfl

theorem coe_dpScalarExtensionEquiv_symm :
    ⇑(dpScalarExtensionEquiv R S M).symm = ⇑(dpScalarExtensionInv R S M) := by
  rfl

theorem rTensor_comp_dpScalarExtensionEquiv_symm_eq {S : Type*} [CommRing S] [Algebra R S]
    {S' : Type*} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (n : ℕ) (m : S ⊗[R] M) :
    φ.toLinearMap.rTensor (DividedPowerAlgebra R M)
        ((dpScalarExtensionEquiv R S M).symm (dp S n m)) =
      (dpScalarExtensionEquiv R S' M).symm (dp S' n (φ.toLinearMap.rTensor M m)) := by
  rw [← coe_map_id₂]
  induction m using TensorProduct.induction_on generalizing n with
  | zero => simp only [dp_null, MonoidWithZeroHom.map_ite_one_zero, map_zero]
  | tmul s m =>
    simp only [coe_dpScalarExtensionEquiv_symm, dpScalarExtensionInv_apply_dp, toLinearMap_apply,
      Algebra.TensorProduct.map_tmul, map_pow, coe_id, id_eq, LinearMap.rTensor_tmul ]
  | add x y hx hy =>
    simp only [dp_add, _root_.map_sum, _root_.map_mul, map_add]
    apply Finset.sum_congr rfl
    rintro ⟨k, l⟩ _
    rw [hx, hy]

    variable {R} {S} {M}

open MvPolynomial

theorem dpScalarExtension_mem_grade {a : DividedPowerAlgebra R M} {n : ℕ} (ha : a ∈ grade R M n)
    (s : S) : dpScalarExtension R S M (s ⊗ₜ[R] a) ∈ grade S (S ⊗[R] M) n := by
  rw [mem_grade_iff]
  set f : R →ₐ[R] S := Algebra.algHom R R S with hf
  obtain ⟨p, hpn, hpa⟩ := ha
  set p' : MvPolynomial (ℕ × M) S := MvPolynomial.baseChange f p with hp'
  use s • rename (Prod.map id (fun m => 1 ⊗ₜ m)) p'
  constructor
  · simp only [SetLike.mem_coe, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous] at hpn ⊢
    intro d' hd'
    simp only [MvPolynomial.coeff_smul, smul_eq_mul] at hd'
    obtain ⟨d, hdd', hd0⟩ := coeff_rename_ne_zero _ _ _ (right_ne_zero_of_mul hd')
    rw [← hdd']
    simp only [hp', hf, coeff_baseChange_apply] at hd0
    have hd0' : coeff d p ≠ 0 := by
      intro h
      simp only [h, map_zero, ne_eq, not_true_eq_false] at hd0
    convert hpn hd0'
    simp only [Finsupp.weight, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_mapDomain]
    rfl
  · have h_eq : (algebraMap S (MvPolynomial (ℕ × M) S)).comp (algebraMap R S) =
      (algebraMap R (MvPolynomial (ℕ × M) S)) := rfl
    have h_eq' : (algebraMap S (DividedPowerAlgebra S (S ⊗[R] M))).comp (algebraMap R S) =
      (algebraMap R (DividedPowerAlgebra S (S ⊗[R] M))) := rfl
    have h_eq'' (d : ℕ × M →₀ ℕ) : MvPolynomial.coeff d ((MvPolynomial.eval₂Hom
          (MvPolynomial.C.comp ↑(Algebra.algHom R R S)) MvPolynomial.X) p) =
            (algebraMap R S) (MvPolynomial.coeff d p) := by
        rw [← MvPolynomial.coeff_map]
        congr
    rw [LinearMapClass.map_smul, dpScalarExtension_tmul]
    congr 1
    simp only [SetLike.mem_coe, mem_weightedHomogeneousSubmodule, IsWeightedHomogeneous] at hpn
    simp only [hp', baseChange, coe_mk, ← hpa, MvPolynomial.rename, ← algebraMap_eq,
      dpScalarExtension, AlgHom.baseChange, toRingHom_eq_coe, coe_mk, RingHom.coe_coe,
      productMap_apply_tmul, _root_.map_one, one_mul, lift', RingQuot.liftAlgHom_mkAlgHom_apply,
      coe_eval₂AlgHom, Function.comp_def, baseChange, hf,  coe_mk]
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_def]
    simp only [eval₂_eq]
    have h_sum (d : ℕ × M →₀ ℕ) : MvPolynomial.coeff d ((MvPolynomial.eval₂Hom
          (MvPolynomial.C.comp ↑(Algebra.algHom R R S)) MvPolynomial.X) p) =
        (coeff d (∑ x ∈ p.support, MvPolynomial.C ((algebraMap R S) (coeff x p)) *
          (monomial x) 1)) := by
      classical
      rw [h_eq'']
      conv_lhs => rw [MvPolynomial.as_sum (p := p)]
      simp only [coeff_sum, MvPolynomial.coeff_C_mul, _root_.map_sum,
        MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero]
      refine Finset.sum_congr rfl (fun x _hx => ?_)
      split_ifs
      · rfl
      · rw [map_zero]
    classical
    rw [Finset.sum_subset_zero_on_sdiff]
    · intro x hx
      simp only [mem_support_iff, ne_eq] at hx ⊢
      simp only [algebraMap_eq, h_sum x, coeff_sum, MvPolynomial.coeff_C_mul, mul_one, mul_zero,
        MvPolynomial.coeff_monomial, mul_ite, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not,
        ite_eq_left_iff, Classical.not_imp] at hx
      exact hx.1
    · intro x hx
      simp only [Finset.mem_sdiff, mem_support_iff, ne_eq, Decidable.not_not, algebraMap_eq,
        h_sum x, coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not, ite_eq_left_iff] at hx
      rw [IsScalarTower.algebraMap_apply R S (DividedPowerAlgebra S (S ⊗[R] M)),
        hx.2 hx.1, map_zero, zero_mul]
    · intro d _hd
      simp only [dp_def]
      rw [← h_eq', RingHom.coe_comp, Function.comp_apply, algebraMap_eq, ← h_eq'', h_sum d,
        coeff_sum, map_sum]
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero]
      rfl

end DividedPowerAlgebra
