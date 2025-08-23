import DividedPowers.PolynomialLaw.Basic2

/-! # Base change of polynomial maps

This file defines a base change map
  `PolynomialLaw R M N →ₗ[R] PolynomialLaw R' (R' ⊗[R] M) (R' ⊗[R] N)``
when M and N are R-modules and R' is an R-algebra (commutative)

## Work in progress

This requires to simplify the tensor product
  `S' ⊗[R'] (R' ⊗[R] M)`
to
  `S' ⊗[R] M`
using an S'-isomorphism — something Mathlib doesn't know (yet)
because TensorProduct.assoc lacks some heteronomy.
This is done in a first part.

Then the base change is defined as a map.

## TODO

- Compare ground
- Extend `PolynomialMap.baseChange` to a linear map.
- Prove that coeff, multiCoeff, biCoeff, commute with base change,
as well as for divided (partial) differentials

-/

namespace TensorProduct

variable {R : Type*} [CommSemiring R]
  {M : Type*}  [AddCommMonoid M] [Module R M]

variable {R' : Type*} [CommSemiring R'] [Algebra R R']
variable {S' : Type*} [CommSemiring S'] [Algebra R' S']
variable {S'' : Type*} [CommSemiring S''] [Algebra R' S'']
variable (φ : S' →ₐ[R'] S'')

variable [Algebra R S'] [IsScalarTower R R' S']
variable [Algebra R S''] [IsScalarTower R R' S'']

/-- an auxiliary map -/
def baseChangeEquiv' : (S' ⊗[R'] R') ⊗[R] M ≃ₗ[S'] S' ⊗[R] M := {
  toAddEquiv := (LinearEquiv.rTensor M ((TensorProduct.rid R' S').restrictScalars R)).toAddEquiv
  map_smul' r' srm := by
    induction srm using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearEquiv.coe_rTensor, smul_add, AddHom.toFun_eq_coe, map_add,
        LinearMap.coe_toAddHom, RingHom.id_apply]
      congr
    | tmul sr m =>
      simp
      rw [smul_tmul']
      simp
      congr
      induction sr using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul s r =>
        rw [← LinearEquiv.eq_symm_apply]
        simp only [rid_tmul, smul_eq_mul, Algebra.mul_smul_comm, map_smul, rid_symm_apply]
        rw [smul_tmul', smul_eq_mul]
        simp [← tmul_smul] }

def baseChangeEquiv :
    S' ⊗[R'] R' ⊗[R] M ≃ₗ[S'] S' ⊗[R] M :=
  (AlgebraTensorModule.assoc R R' S' S' R' M).symm.trans baseChangeEquiv'

theorem baseChangeEquiv_rTensor_baseChangeEquivSymm (y : S' ⊗[R] M) :
    baseChangeEquiv
      ((LinearMap.rTensor (R' ⊗[R] M) φ.toLinearMap) ((baseChangeEquiv (R' := R')).symm y)) =
      LinearMap.rTensor M ((φ.restrictScalars R).toLinearMap) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s n => simp [baseChangeEquiv, baseChangeEquiv']

theorem baseChangeEquiv_rTensor_eq_baseChangeEquivSymm_rTensor (x : S' ⊗[R'] R' ⊗[R] M) :
    baseChangeEquiv ((LinearMap.rTensor (R' ⊗[R] M) φ.toLinearMap) x) =
      LinearMap.rTensor M ((φ.restrictScalars R).toLinearMap) (baseChangeEquiv x) := by
  set y := baseChangeEquiv x with hy
  rw [← LinearEquiv.eq_symm_apply] at hy
  rw [hy, baseChangeEquiv_rTensor_baseChangeEquivSymm]

end TensorProduct

namespace PolynomialLaw

open TensorProduct

universe u v w
variable {R : Type u} [CommSemiring R]
  {M : Type*}  [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]

variable (R' : Type v) [CommSemiring R'] [Algebra R R']

/-- The base change of a polynomial law. -/
noncomputable def baseChange (f : M →ₚₗ[R] N) :
    (R' ⊗[R] M) →ₚₗ[R'] (R' ⊗[R] N) where
  toFun' S' _ _ srm := by
    let _ : Algebra R S' := RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    have _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq
      (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    exact baseChangeEquiv.symm (f.toFun S' (baseChangeEquiv srm))
  isCompat' {S' _ _ S'' _ _} φ := by
    let _ : Algebra R S' := RingHom.toAlgebra ((algebraMap R' S').comp (algebraMap R R'))
    have _ : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq
      (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    let _ : Algebra R S'' := RingHom.toAlgebra ((algebraMap R' S'').comp (algebraMap R R'))
    have _ : IsScalarTower R R' S'' := IsScalarTower.of_algebraMap_eq
      (fun r ↦ by simp [RingHom.algebraMap_toAlgebra])
    ext srm
    dsimp only
    symm
    simp only [Function.comp_apply]
    rw [LinearEquiv.symm_apply_eq]
    rw [baseChangeEquiv_rTensor_eq_baseChangeEquivSymm_rTensor]
    rw [baseChangeEquiv_rTensor_baseChangeEquivSymm]
    rw [← f.isCompat_apply]

def baseChange_linearMap : (M →ₚₗ[R] N) →ₗ[R] RestrictScalars R R' ((R' ⊗[R] M) →ₚₗ[R'] (R' ⊗[R] N)) where
  toFun := baseChange R'
  map_add' f g := sorry
  map_smul' r f := sorry

theorem baseChange_ground (f : M →ₚₗ[R] N) :
    (f.baseChange R').ground = f.toFun R' := by
  sorry

end PolynomialLaw
