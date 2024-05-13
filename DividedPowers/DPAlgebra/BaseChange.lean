import DividedPowers.DPAlgebra.Init
import DividedPowers.DPAlgebra.Exponential
import DividedPowers.DPAlgebra.Misc
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

The existence of the base change morphism  is relatively straightforward,
but the existence of the morphism in the other direction is nontrivial.
As in [Roby1963], the proof relies on the `ExponentialModule` that allows
to linearize the divided power algebra, and then we apply the standard
base change adjunction for linear maps.

-/
universe u

open scoped TensorProduct

section baseChange

variable (R : Type*) [CommRing R]
  (S : Type*) [CommRing S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- The base change adjunction for linear maps -/
noncomputable def LinearMap.baseChangeEquiv : (S ⊗[R] M →ₗ[S] N) ≃ₗ[S] (M →ₗ[R] N) where
  toFun g := LinearMap.comp (g.restrictScalars R) ({
    toFun := fun m ↦ 1 ⊗ₜ[R] m
    map_add' := fun x y ↦ by simp only [TensorProduct.tmul_add]
    map_smul' := fun r x ↦ by
      simp only [TensorProduct.tmul_smul, RingHom.id_apply] } : M →ₗ[R] S ⊗[R] M)
  invFun f := TensorProduct.AlgebraTensorModule.lift ((LinearMap.lsmul S (M →ₗ[R] N)).flip f)
  left_inv g := by ext m; simp
  right_inv f := by ext m; simp
  map_add' _ _ := by ext m; simp
  map_smul' s g := by ext m; simp

end baseChange



namespace DividedPowerAlgebra

open Algebra.TensorProduct DividedPowers DividedPowerAlgebra

/-- base change morphism for morphism of algebras -/
noncomputable def AlgHom.baseChange
    {R A B C : Type _} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B]
    [CommSemiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C] (φ : B →ₐ[R] C) :
    A ⊗[R] B →ₐ[A] C :=
  { Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R A C) φ with
    commutes' := fun r => by
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
        AlgHom.toFun_eq_coe, Algebra.TensorProduct.productMap_apply_tmul,
        IsScalarTower.coe_toAlgHom', map_one, _root_.mul_one] }
#align alg_hom.base_change DividedPowerAlgebra.AlgHom.baseChange

theorem AlgHom.baseChange_tmul
    {R A B C : Type _} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B]
    [CommSemiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    (φ : B →ₐ[R] C) (a : A) (b : B) :
    AlgHom.baseChange φ (a ⊗ₜ[R] b) = a • (φ b) := by
  simp only [baseChange, AlgHom.toRingHom_eq_coe, AlgHom.coe_mk,
    RingHom.coe_coe, productMap_apply_tmul, IsScalarTower.coe_toAlgHom']
  rw [← smul_eq_mul, algebraMap_smul]

noncomputable def _root_.TensorProduct.includeRight {R S N : Type _} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid N] [Module R N] :
    N →ₗ[R] S ⊗[R] N where
  toFun := fun n ↦ 1 ⊗ₜ n
  map_add' := fun x y ↦ TensorProduct.tmul_add 1 x y
  map_smul' := fun r x ↦ by
    simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', RingHom.id_apply]

--TODO : prove uniqueness
/-- A base change morphism for the divided power algebra
[Roby1963, Proposition III.4] -/
noncomputable def dpScalarExtension'
    (R : Type u) [CommSemiring R]
    (S : Type _) [CommSemiring S] [Algebra R S]
    (M : Type _) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M] :
    S ⊗[R] DividedPowerAlgebra R M →ₐ[S] DividedPowerAlgebra S M := by
  apply AlgHom.baseChange
  apply lift' fun nm => dp S nm.1 nm.2
  · intro m; dsimp only; rw [dp_zero]
  · intro n r m; dsimp only
    rw [← algebraMap_smul S r m, dp_smul S (algebraMap R S r) n m, ← map_pow, algebraMap_smul]
  · intro n p m; dsimp only; rw [dp_mul]
  · intro n x y; dsimp only; rw [dp_add]
#align divided_power_algebra.dp_scalar_extension' DividedPowerAlgebra.dpScalarExtension'


section dpScalarExtension

variable (A : Type*) [CommSemiring A]
    (R : Type*) [CommSemiring R] [Algebra A R]
    (M : Type*) [AddCommMonoid M] [Module A M]

noncomputable
def dpScalarExtension :
    R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M) := by
  apply AlgHom.baseChange
  apply lift'
    (fun nm => dp R nm.1 (1 ⊗ₜ[A] nm.2) : ℕ × M → DividedPowerAlgebra R (R ⊗[A] M))
  · intro m; dsimp only; rw [dp_zero]
  · intro n a m; dsimp only; simp only [TensorProduct.tmul_smul]
    rw [← algebraMap_smul R a]; rw [dp_smul]
    rw [← map_pow]; rw [algebraMap_smul R]
  · intro n p m; dsimp only; rw [dp_mul]
  · intro n x y; dsimp only; simp only [TensorProduct.tmul_add]; rw [dp_add]
#align divided_power_algebra.dp_scalar_extension DividedPowerAlgebra.dpScalarExtension

theorem dpScalarExtension_apply (r : R) (n : ℕ) (m : M) :
    dpScalarExtension A R M ((r ^ n) ⊗ₜ[A] (dp A n m)) = dp R n (r ⊗ₜ[A] m) := by
  simp [dpScalarExtension]
  simp [AlgHom.baseChange_tmul, lift'AlgHom_apply_dp]
  rw [← dp_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end dpScalarExtension
variable
    (R : Type*) [CommRing R]
    (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M]

noncomputable def dpScalarExtensionExp :
    S ⊗[R] M →ₗ[S] ExponentialModule (S ⊗[R] DividedPowerAlgebra R M) :=
  (LinearMap.baseChangeEquiv R S M (ExponentialModule (S ⊗[R] DividedPowerAlgebra R M))).symm
    ((ExponentialModule.linearMap (Algebra.TensorProduct.includeRight)).comp (exp_LinearMap R M))

noncomputable
def dpScalarExtensionInv  :
    DividedPowerAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] DividedPowerAlgebra R M :=
  (dividedPowerAlgebra_exponentialModule_equiv S (S ⊗[R] M) (S ⊗[R] DividedPowerAlgebra R M)).symm (dpScalarExtensionExp R S M)

-- TODO : add uniqueness of `dpScalarExtensionInv` satisfying this
/-- Roby1963, theorem III.2 -/
theorem dpScalarExtensionInv_apply (n : ℕ) (s : S) (m : M) :
    dpScalarExtensionInv R S M (dp S n (s ⊗ₜ[R] m)) = (s ^ n) ⊗ₜ[R] (dp R n m) := by
  simp [dpScalarExtensionInv]
  rw [dividedPowerAlgebra_exponentialModule_equiv_symm_apply]
  simp [dpScalarExtensionExp, LinearMap.baseChangeEquiv]
  simp only [ExponentialModule.coe_smul]
  simp only [PowerSeries.coeff_scale]
  simp only [ExponentialModule.coeff_linearMap]
  simp [includeRight]
  simp only [coeff_exp_LinearMap]
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

noncomputable example (R : Type _) [CommSemiring R]
    (A : Type _) [CommSemiring A] [Algebra R A]
    (S : Type _) [CommSemiring S] [Algebra R S] :
  Algebra S (S ⊗[R] A) := inferInstance

/-- The base change isomorphism for the divided power algebra

[Roby1963, theorem III.3] -/
noncomputable
def dpScalarExtensionEquiv :
  S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom (dpScalarExtension R S M) (dpScalarExtensionInv R S M)
    (by
      apply DividedPowerAlgebra.ext
      rintro n sm
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
      revert n
      induction sm using TensorProduct.induction_on with
      | zero =>
        intro n
        rw [dp_null]
        split_ifs
        · simp only [map_one]
        · simp only [map_zero]
      | tmul s m =>
        intro n
        rw [dpScalarExtensionInv_apply, dpScalarExtension_apply]
      | add x y hx hy =>
        intro n
        rw [dp_add, map_sum, map_sum]
        apply Finset.sum_congr rfl
        rintro ⟨k, l⟩ hkl
        rw [map_mul, map_mul, hx, hy])
    (by
      apply Algebra.TensorProduct.ext
      · ext
      · apply DividedPowerAlgebra.ext
        intro n m
        simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars',
          Function.comp_apply, includeRight_apply, AlgHom.coe_id, id_eq]
        rw [← one_pow n, dpScalarExtension_apply, dpScalarExtensionInv_apply])

end DividedPowerAlgebra
