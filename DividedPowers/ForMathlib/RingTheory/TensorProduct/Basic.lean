/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The tensor product of R-algebras

We define base change of linear forms, base change of morphism of algebras and the base change
adjunction for linear maps, and provide some rewriting lemmas for tensor products with the
identity map.

## Main definitions

* `LinearForm.baseChange S f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

* `LinearMap.baseChangeEquiv` : the base change adjunction for linear maps.

* `AlgHom.baseChange` : base change morphism for morphism of algebras.

-/

namespace LinearForm

open Algebra Algebra.TensorProduct Function LinearMap TensorProduct

variable {R S S' M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') [AddCommMonoid M] [Module R M] (f : M →ₗ[R] R)

variable (S) in
/-- `baseChange S f` for `f : M →ₗ[R] R` is the `S`-linear map `S ⊗[R] M →ₗ[S] S`.

This "base change" operation is also known as "extension of scalars". -/
noncomputable def baseChange : S ⊗[R] M →ₗ[S] S :=
  (Algebra.TensorProduct.rid R S S).toLinearMap.comp (f.baseChange S)

theorem baseChange_apply_tmul (r : S) (m : M) :
    baseChange S f (r ⊗ₜ[R] m) = r * ((f m) • (1 : S)) := by
  simp [baseChange, coe_comp, Function.comp_apply, baseChange_tmul, AlgEquiv.toLinearMap_apply,
    rid_tmul, Algebra.mul_smul_comm, mul_one]

theorem baseChange_compat_apply (m : S ⊗[R] M) :
    φ (baseChange S f m) = (baseChange S' f) ((rTensor M φ.toLinearMap) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul => simp [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
      AlgEquiv.toLinearMap_apply, rid_tmul, map_smul, rTensor_tmul, AlgHom.toLinearMap_apply]
  | add x y hx hy => simp [map_add, hx, hy]

end LinearForm

section TensorProduct

variable (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S] [Algebra R S]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

open TensorProduct

/-- The base change adjunction for linear maps. -/
noncomputable def LinearMap.baseChangeEquiv : (S ⊗[R] M →ₗ[S] N) ≃ₗ[S] (M →ₗ[R] N) where
  toFun g := LinearMap.comp (g.restrictScalars R) ({
    toFun       := fun m ↦ 1 ⊗ₜ[R] m
    map_add'    := fun x y ↦ by simp [tmul_add]
    map_smul'   := fun r x ↦ by simp [tmul_smul, RingHom.id_apply] } : M →ₗ[R] S ⊗[R] M)
  invFun f      := AlgebraTensorModule.lift ((LinearMap.lsmul S (M →ₗ[R] N)).flip f)
  left_inv g    := by ext; simp
  right_inv f   := by ext; simp
  map_add' _ _  := by ext; simp
  map_smul' s g := by ext; simp

variable {R S N}
noncomputable def TensorProduct.includeRight : N →ₗ[R] S ⊗[R] N where
  toFun     := fun n ↦ 1 ⊗ₜ n
  map_add'  := fun x y ↦ tmul_add 1 x y
  map_smul' := fun r x ↦ by simp only [tmul_smul, smul_tmul', RingHom.id_apply]

end TensorProduct

lemma Algebra.TensorProduct.coe_map_id₁ (R : Type*) [CommSemiring R]
    {S S' : Type*} [Semiring S] [Semiring S'] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') (A : Type*) [Semiring A] [Algebra R A] :
    ⇑(Algebra.TensorProduct.map (AlgHom.id R A) φ) = ⇑(LinearMap.lTensor A φ.toLinearMap) := by rfl

lemma Algebra.TensorProduct.coe_map_id₂ (R : Type*) [CommSemiring R]
    {S S' : Type*} [Semiring S] [Semiring S'] [Algebra R S] [Algebra R S']
    (φ : S →ₐ[R] S') (A : Type*) [Semiring A] [Algebra R A] :
    ⇑(Algebra.TensorProduct.map φ (AlgHom.id R A)) = ⇑(LinearMap.rTensor A φ.toLinearMap) := by rfl

section BaseChange

open Algebra.TensorProduct TensorProduct

/-- Base change morphism for morphism of algebras. -/
protected noncomputable def AlgHom.baseChange {R A B C : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C] [Algebra A C]
    [IsScalarTower R A C] (φ : B →ₐ[R] C) : A ⊗[R] B →ₐ[A] C :=
  { productMap (IsScalarTower.toAlgHom R A C) φ with
    commutes' := fun r => by
      simp only [algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, toFun_eq_coe,
        productMap_apply_tmul, IsScalarTower.coe_toAlgHom', _root_.map_one, _root_.mul_one] }

theorem AlgHom.baseChange_tmul {R A B C : Type _} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C] [Algebra A C]
    [IsScalarTower R A C] (φ : B →ₐ[R] C) (a : A) (b : B) :
    φ.baseChange (a ⊗ₜ[R] b) = a • (φ b) := by
  simp only [AlgHom.baseChange, toRingHom_eq_coe, coe_mk, RingHom.coe_coe, productMap_apply_tmul,
    IsScalarTower.coe_toAlgHom', ← smul_eq_mul, algebraMap_smul]

end BaseChange
