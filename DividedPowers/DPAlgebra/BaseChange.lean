import DividedPowers.DPAlgebra.Init
import DividedPowers.DPAlgebra.Misc
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic

-- import DividedPowers.ForMathlib.RingTheory.TensorProduct

universe u

open scoped TensorProduct

namespace DividedPowerAlgebra

open Algebra.TensorProduct DividedPowers DividedPowerAlgebra

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

noncomputable def _root_.TensorProduct.includeRight {R S N : Type _} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid N] [Module R N] :
    N →ₗ[R] S ⊗[R] N where
  toFun := fun n ↦ 1 ⊗ₜ n
  map_add' := fun x y ↦ TensorProduct.tmul_add 1 x y
  map_smul' := fun r x ↦ by
    simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', RingHom.id_apply]

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

noncomputable
def dpScalarExtension (A : Type _) [CommSemiring A] (R : Type _) [CommSemiring R]
    [Algebra A R] (M : Type _) [AddCommMonoid M] [Module A M] :
    R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M) :=
  by
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

--noncomputable
def dpScalarExtensionInv (R : Type _) [CommSemiring R]
    (S : Type _) [CommSemiring S] [Algebra R S]
    (M : Type _) [AddCommMonoid M] [Module R M] :
  DividedPowerAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] DividedPowerAlgebra R M := by
  -- TODO: Roby's proof uses the exponential module
  sorry


#align divided_power_algebra.dp_scalar_extension_inv DividedPowerAlgebra.dpScalarExtensionInv

noncomputable instance (R : Type _) [CommSemiring R]
    (A : Type _) [CommSemiring A] [Algebra R A]
    (S : Type _) [CommSemiring S] [Algebra R S] :
  Algebra S (S ⊗[R] A) := inferInstance

/- let f : ℕ × M → R ⊗[A] (divided_power_algebra A M) :=
  λ nm, algebra.tensor_product.include_right (dp A nm.1 nm.2),
  apply lift_aux R M (λ nm, algebra.tensor_product.include_right (dp A nm.1 nm.2)),
  { intro m, dsimp only, rw dp_zero, rw map_one, },
  { intros n r m, dsimp only,
  -- does not seem obvious !
    sorry, },
  { intros n p m, dsimp only, rw [← map_mul, ← map_nsmul,dp_mul], },
  { intros n x y, dsimp only, simp_rw [← map_mul, ← map_sum], rw dp_add, } -/
-- TODO ! But in Roby, this follows from the exponential power series interpretation
noncomputable
def dpScalarExtensionEquiv (R : Type _) [CommSemiring R]
    (S : Type _) [CommSemiring S] [Algebra R S]
    (M : Type _) [AddCommMonoid M] [Module R M] :
  S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom
    (dpScalarExtension R S M)
    (dpScalarExtensionInv R S M)
    (sorry)
    (sorry)


#align divided_power_algebra.dp_scalar_extension_equiv DividedPowerAlgebra.dpScalarExtensionEquiv

end DividedPowerAlgebra
