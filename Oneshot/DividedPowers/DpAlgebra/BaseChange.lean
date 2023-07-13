import Oneshot.DividedPowers.DpAlgebra.Init
import Oneshot.DividedPowers.DpAlgebra.Misc
import Mathbin.Algebra.Algebra.Operations
import Mathbin.RingTheory.MvPolynomial.Basic
import Oneshot.ForMathlib.RingTheory.TensorProduct

universe u

open scoped TensorProduct

namespace DividedPowerAlgebra

def AlgHom.baseChange {A B C R : Type _} [CommRing A] [CommRing B] [Algebra A B] [CommRing R]
    [Algebra A R] [CommRing C] [Algebra A C] [Algebra R C] [IsScalarTower A R C] (φ : B →ₐ[A] C) :
    R ⊗[A] B →ₐ[R] C :=
  { Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom A R C) φ with
    commutes' := fun r => by
      simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
        AlgHom.toFun_eq_coe, Algebra.TensorProduct.productMap_apply_tmul,
        IsScalarTower.coe_toAlgHom', map_one, mul_one] }
#align alg_hom.base_change AlgHom.baseChange

noncomputable def dpScalarExtension' (A : Type u) [CommRing A] (R : Type u) [CommRing R]
    [Algebra A R] (M : Type u) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M] :
    R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R M :=
  by
  apply AlgHom.baseChange
  apply lift_aux A M fun nm => dp R nm.1 nm.2
  · intro m; dsimp only; rw [dp_zero]
  · intro n r m; dsimp only
    rw [← algebraMap_smul R r m, dp_smul R (algebraMap A R r) n m, ← map_pow, algebraMap_smul]
  · intro n p m; dsimp only; rw [dp_mul]
  · intro n x y; dsimp only; rw [dp_add]
#align divided_power_algebra.dp_scalar_extension' DividedPowerAlgebra.dpScalarExtension'

noncomputable def dpScalarExtension (A : Type u) [CommRing A] (R : Type u) [CommRing R]
    [Algebra A R] (M : Type u) [AddCommGroup M] [Module A M] :
    R ⊗[A] DividedPowerAlgebra A M →ₐ[R] DividedPowerAlgebra R (R ⊗[A] M) :=
  by
  apply AlgHom.baseChange
  apply lift_aux A M (fun nm => dp R nm.1 (1 ⊗ₜ[A] nm.2) : ℕ × M → DividedPowerAlgebra R (R ⊗[A] M))
  · intro m; dsimp only; rw [dp_zero]
  · intro n a m; dsimp only; simp only [TensorProduct.tmul_smul]
    rw [← algebraMap_smul R a]; rw [dp_smul]
    rw [← map_pow]; rw [algebraMap_smul R]
    infer_instance
    infer_instance
  · intro n p m; dsimp only; rw [dp_mul]
  · intro n x y; dsimp only; simp only [TensorProduct.tmul_add]; rw [dp_add]
#align divided_power_algebra.dp_scalar_extension DividedPowerAlgebra.dpScalarExtension

--noncomputable
def dpScalarExtensionInv (A : Type u) [CommRing A] (R : Type u) [CommRing R] [Algebra A R]
    (M : Type u) [AddCommGroup M] [Module A M] :
    DividedPowerAlgebra R (R ⊗[A] M) →ₐ[R] R ⊗[A] DividedPowerAlgebra A M :=
  by-- TODO: There is an error in this proof
  sorry
#align divided_power_algebra.dp_scalar_extension_inv DividedPowerAlgebra.dpScalarExtensionInv

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
def dpScalarExtensionEquiv (A : Type _) [CommRing A] (R : Type _) [CommRing R] [Algebra A R]
    (M : Type _) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M] :
    R ⊗[A] DividedPowerAlgebra A M ≃ₐ[R] DividedPowerAlgebra R M :=
  sorry
#align divided_power_algebra.dp_scalar_extension_equiv DividedPowerAlgebra.dpScalarExtensionEquiv

end DividedPowerAlgebra

