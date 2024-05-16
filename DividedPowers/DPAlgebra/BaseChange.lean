--import DividedPowers.DPAlgebra.Init
import DividedPowers.DPAlgebra.Exponential
--import DividedPowers.DPAlgebra.Misc
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic

-- import DividedPowers.ForMathlib.RingTheory.TensorProduct
/-! # Base change properties of the divided power algebra


The file starts with complements, to dispatch elsewhere,
regarding base change of algebras/modules.

The main result is the construction of a base change isomorphism
for the divided power algebra:

* `dpScalarExtensionEquiv :
  S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M)`
(Theorem III.3 of [Roby1963])
* `dpScalarExtension_apply` and `dpScalarExtensionInv_apply` compute
its action on basic elements in both directions.

## Note on the proof

The existence of the base change morphism is relatively straightforward,
but the existence of the morphism in the other direction is nontrivial.
As in [Roby1963], the proof relies on the `ExponentialModule` that allows
to linearize the divided power algebra, and then we apply the standard
base change adjunction for linear maps.

-/
universe u

open scoped TensorProduct
open AlgHom TensorProduct

section baseChange

lemma Algebra.TensorProduct.coe_map_id₁ (R : Type*) [CommSemiring R]
    {S S' : Type*} [Semiring S] [Semiring S'] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') (A : Type*) [Semiring A] [Algebra R A] :
    ⇑(Algebra.TensorProduct.map (AlgHom.id R A) φ) = ⇑(LinearMap.lTensor A φ.toLinearMap) := by rfl

lemma Algebra.TensorProduct.coe_map_id₂ (R : Type*) [CommSemiring R]
    {S S' : Type*} [Semiring S] [Semiring S'] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') (A : Type*) [Semiring A] [Algebra R A] :
    ⇑(Algebra.TensorProduct.map φ (AlgHom.id R A)) = ⇑(LinearMap.rTensor A φ.toLinearMap) := by rfl

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The base change adjunction for linear maps -/
noncomputable def LinearMap.baseChangeEquiv : (S ⊗[R] M →ₗ[S] N) ≃ₗ[S] (M →ₗ[R] N) where
  toFun g := LinearMap.comp (g.restrictScalars R) ({
    toFun       := fun m ↦ 1 ⊗ₜ[R] m
    map_add'    := fun x y ↦ by simp only [tmul_add]
    map_smul'   := fun r x ↦ by simp only [tmul_smul, RingHom.id_apply] } : M →ₗ[R] S ⊗[R] M)
  invFun f      := AlgebraTensorModule.lift ((LinearMap.lsmul S (M →ₗ[R] N)).flip f)
  left_inv g    := by ext m; simp
  right_inv f   := by ext m; simp
  map_add' _ _  := by ext m; simp
  map_smul' s g := by ext m; simp

end baseChange

namespace DividedPowerAlgebra

open Algebra.TensorProduct DividedPowers DividedPowerAlgebra

/-- base change morphism for morphism of algebras -/
noncomputable def AlgHom.baseChange {R A B C : Type _} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C] [Algebra A C]
    [IsScalarTower R A C] (φ : B →ₐ[R] C) : A ⊗[R] B →ₐ[A] C :=
  { productMap (IsScalarTower.toAlgHom R A C) φ with
    commutes' := fun r => by
      simp only [algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply, toFun_eq_coe,
        productMap_apply_tmul, IsScalarTower.coe_toAlgHom', _root_.map_one, _root_.mul_one] }

theorem AlgHom.baseChange_tmul {R A B C : Type _} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C] [Algebra A C]
    [IsScalarTower R A C] (φ : B →ₐ[R] C) (a : A) (b : B) :
    baseChange φ (a ⊗ₜ[R] b) = a • (φ b) := by
  simp only [baseChange, toRingHom_eq_coe, coe_mk, RingHom.coe_coe, productMap_apply_tmul,
    IsScalarTower.coe_toAlgHom', ← smul_eq_mul, algebraMap_smul]

noncomputable def _root_.TensorProduct.includeRight {R S N : Type _} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid N] [Module R N] :
    N →ₗ[R] S ⊗[R] N where
  toFun     := fun n ↦ 1 ⊗ₜ n
  map_add'  := fun x y ↦ tmul_add 1 x y
  map_smul' := fun r x ↦ by simp only [tmul_smul, smul_tmul', RingHom.id_apply]

--TODO : prove uniqueness
/-- A base change morphism for the divided power algebra
[Roby1963, Proposition III.4] -/
noncomputable def dpScalarExtension' (R : Type u) [CommSemiring R] (S : Type _) [CommSemiring S]
    [Algebra R S] (M : Type _) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] :
    S ⊗[R] DividedPowerAlgebra R M →ₐ[S] DividedPowerAlgebra S M := by
  apply AlgHom.baseChange
  apply lift' fun nm => dp S nm.1 nm.2
  · intro m; rw [dp_zero]
  · intro n r m
    rw [← algebraMap_smul S r m, dp_smul S (algebraMap R S r) n m, ← map_pow, algebraMap_smul]
  · intro n p m; rw [dp_mul]
  · intro n x y; rw [dp_add]

section dpScalarExtension

variable (A : Type*) [CommSemiring A] (R : Type*) [CommSemiring R] [Algebra A R]
    (M : Type*) [AddCommMonoid M] [Module A M]

noncomputable def dpScalarExtension :
    R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M) := by
  apply AlgHom.baseChange
  apply lift' (fun nm => dp R nm.1 (1 ⊗ₜ[A] nm.2) : ℕ × M → DividedPowerAlgebra R (R ⊗[A] M))
  · intro m; rw [dp_zero]
  · intro n a m; simp only [tmul_smul]
    rw [← algebraMap_smul R a, dp_smul, ← map_pow, algebraMap_smul R]
  · intro n p m; rw [dp_mul]
  · intro n x y; rw [tmul_add, dp_add]

theorem dpScalarExtension_apply (r : R) (n : ℕ) (m : M) :
    dpScalarExtension A R M ((r ^ n) ⊗ₜ[A] (dp A n m)) = dp R n (r ⊗ₜ[A] m) := by
  rw [dpScalarExtension, AlgHom.baseChange_tmul, lift'AlgHom_apply_dp, ← dp_smul, smul_tmul',
    smul_eq_mul, mul_one]

theorem dpScalarExtension_apply_one (n : ℕ) (m : M) :
    dpScalarExtension A R M (1 ⊗ₜ[A] (dp A n m)) = dp R n (1 ⊗ₜ[A] m) := by
  rw [← one_pow n, dpScalarExtension_apply, one_pow]

/-- Uniqueness for [Roby1963, Theorem III.2] (opposite map) -/
theorem dpScalarExtension_unique
  {φ : R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M)}
  (hφ : ∀ (n : ℕ) (m : M), φ (1 ⊗ₜ[A] (dp A n m)) = dp R n (1 ⊗ₜ[A] m) ) :
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
          dpScalarExtension_apply_one]
  | add x y hx hy => simp only [map_add, hx, hy]

end dpScalarExtension

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M]

noncomputable def dpScalarExtensionExp :
    S ⊗[R] M →ₗ[S] ExponentialModule (S ⊗[R] DividedPowerAlgebra R M) :=
  (LinearMap.baseChangeEquiv R S M (ExponentialModule (S ⊗[R] DividedPowerAlgebra R M))).symm
    ((ExponentialModule.linearMap Algebra.TensorProduct.includeRight).comp (exp_LinearMap R M))

noncomputable def dpScalarExtensionInv  :
    DividedPowerAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] DividedPowerAlgebra R M :=
  (dividedPowerAlgebra_exponentialModule_equiv S (S ⊗[R] M)
    (S ⊗[R] DividedPowerAlgebra R M)).symm (dpScalarExtensionExp R S M)

-- TODO : add uniqueness of `dpScalarExtensionInv` satisfying this
/-- Roby1963, theorem III.2 -/
theorem dpScalarExtensionInv_apply (n : ℕ) (s : S) (m : M) :
    dpScalarExtensionInv R S M (dp S n (s ⊗ₜ[R] m)) = (s ^ n) ⊗ₜ[R] (dp R n m) := by
  rw [dpScalarExtensionInv, dividedPowerAlgebra_exponentialModule_equiv_symm_apply]
  simp only [dpScalarExtensionExp, LinearMap.baseChangeEquiv, LinearEquiv.coe_symm_mk,
    AlgebraTensorModule.lift_apply, lift.tmul, LinearMap.coe_restrictScalars, LinearMap.flip_apply,
    LinearMap.lsmul_apply, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [ExponentialModule.coe_smul, PowerSeries.coeff_scale, ExponentialModule.coeff_linearMap,
    Algebra.TensorProduct.includeRight, coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, coeff_exp_LinearMap, smul_tmul', smul_eq_mul, mul_one]

noncomputable example (R : Type*) [CommSemiring R] (A : Type*) [CommSemiring A] [Algebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] : Algebra S (S ⊗[R] A) := inferInstance

/-- The base change isomorphism for the divided power algebra

[Roby1963, theorem III.3] -/
noncomputable def dpScalarExtensionEquiv :
    S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom (dpScalarExtension R S M) (dpScalarExtensionInv R S M)
    (by
      apply DividedPowerAlgebra.ext
      rintro n sm
      simp only [coe_comp, Function.comp_apply, coe_id, id_eq]
      induction sm using TensorProduct.induction_on generalizing n with
      | zero =>
        rw [dp_null]
        split_ifs
        · simp only [_root_.map_one]
        · simp only [map_zero]
      | tmul s m =>
        rw [dpScalarExtensionInv_apply, dpScalarExtension_apply]
      | add x y hx hy =>
        rw [dp_add, map_sum, map_sum]
        apply Finset.sum_congr rfl
        rintro ⟨k, l⟩ _
        rw [_root_.map_mul, _root_.map_mul, hx, hy])
    (by
      apply Algebra.TensorProduct.ext
      · ext
      · apply DividedPowerAlgebra.ext
        intro n m
        simp only [coe_comp, coe_restrictScalars', Function.comp_apply, includeRight_apply,
          coe_id, id_eq]
        rw [← one_pow n, dpScalarExtension_apply, dpScalarExtensionInv_apply])

theorem coe_dpScalarExtensionEquiv :
    ⇑(dpScalarExtensionEquiv R S M) = ⇑(dpScalarExtension R S M) := by
  rfl

theorem coe_dpScalarExtensionEquiv_symm :
    ⇑(dpScalarExtensionEquiv R S M).symm = ⇑(dpScalarExtensionInv R S M) := by
  rfl

/- Once one replaces (dpScalarExtensionEquiv _ _ _).symm
  by dpScalarExtensionInv,
  the following proof is very close to the 3rd step of the proof of the dpScalarExtensionEquiv.
  Can one unify them? -/

theorem rTensor_comp_dpScalarExtensionEquiv_symm_eq {S : Type*} [CommRing S] [Algebra R S]
    {S' : Type*} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (n : ℕ) (m : S ⊗[R] M) :
    φ.toLinearMap.rTensor (DividedPowerAlgebra R M)
        ((dpScalarExtensionEquiv R S M).symm (dp S n m)) =
      (dpScalarExtensionEquiv R S' M).symm (dp S' n (φ.toLinearMap.rTensor M m)) := by
  rw [← coe_map_id₂]
  induction m using TensorProduct.induction_on generalizing n with
  | zero => simp only [Function.comp_apply, dp_null, RingHom.map_ite_one_zero, map_zero]
  | tmul s m =>
    simp only [coe_dpScalarExtensionEquiv_symm, dpScalarExtensionInv_apply, toLinearMap_apply,
      Algebra.TensorProduct.map_tmul, map_pow, coe_id, id_eq, LinearMap.rTensor_tmul ]
  | add x y hx hy =>
    simp only [dp_add, _root_.map_sum, _root_.map_mul, map_add]
    apply Finset.sum_congr rfl
    rintro ⟨k, l⟩ _
    rw [hx, hy]

end DividedPowerAlgebra
