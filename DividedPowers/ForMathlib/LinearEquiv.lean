import Mathlib.LinearAlgebra.TensorProduct.Basic

open scoped TensorProduct

variable {R : Type*} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]

/-- Tensor a linear equivalence to the right gives a linear equivalence -/
noncomputable def LinearEquiv.rTensor
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[R] N) :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)

/-- Tensor a linear equivalence to the left gives a linear equivalence -/
noncomputable def LinearEquiv.lTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    P ⊗[R] M ≃ₗ[R] P ⊗[R] N := TensorProduct.congr (refl R P) e
