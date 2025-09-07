/-
Copyright (c) 2024 Antoine Chambert-Loir and María Inés de Frutos Fernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir and María Inés de Frutos Fernandez.
-/

import Mathlib.RingTheory.TensorProduct.Basic

/-! # Linear Equivalences on tensor products

* `LinearEquiv.rTensor`, `LinearEquiv.lTensor` : tensor a linear equivalence
  to the right or to the left gives a linear equivalence;
* `LinearEquiv.rTensor'`, `LinearEquiv.lTensor'` : tensor a linear equivalence
  to the right or to the left gives a linear equivalence, with more `smul` properties;

-/

universe u v w

variable {R : Type u} {M : Type v} {N : Type w} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

open LinearMap

variable [AddCommMonoid N] [Module R N]

variable [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P] {Q : Type*} [AddCommMonoid Q] [Module R Q]

namespace TensorProduct

/--  If `e` is `S`-linear, then `TensorProduct.map e f` is `S`-linear -/
noncomputable def map' (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    M ⊗[R] P →ₗ[S] N ⊗[R] Q where
  toFun := map (e.restrictScalars R) f
  map_add' := map_add _
  map_smul' s t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp [hx, hy]
    | tmul m p => simp [map_tmul, coe_restrictScalars, map_smul, smul_tmul']

@[simp]
theorem map'_restrictScalars (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    (map' e f).restrictScalars R = map (e.restrictScalars R) f := rfl

@[simp]
theorem map'_coe (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    ⇑(map' e f) = ⇑(map (e.restrictScalars R) f) := rfl

@[simp]
theorem map'_tmul (e : M →ₗ[S] N) (f : P →ₗ[R] Q) (m : M) (p : P) :
      map' e f (m ⊗ₜ p) = (e m) ⊗ₜ (f p) := rfl

/--  If `e` is a `S`-linear equivalence and `f` is an `R`-linear equivalence,
  then `TensorProduct.congr' e f` is a `S`-linear equivalence -/
noncomputable def congr'
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) : M ⊗[R] P ≃ₗ[S] N ⊗[R] Q :=
  LinearEquiv.ofLinear (map' e f) (map' e.symm.toLinearMap f.symm) (by ext; simp) (by ext; simp)

@[simp]
theorem congr'_restrictScalars (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    (congr' e f).restrictScalars R = (congr (e.restrictScalars R) f) := rfl

@[simp]
theorem congr'_coe (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    ⇑(congr' e f) = ⇑(congr (e.restrictScalars R) f) := by rfl

end TensorProduct

variable (P) (e : M ≃ₗ[S] N)

namespace LinearEquiv

open TensorProduct

/-- Tensor a linear equivalence to the right or to the left gives a linear equivalence-/
noncomputable def rTensor' : M ⊗[R] P ≃ₗ[S] N ⊗[R] P :=
  congr' e (LinearEquiv.refl R P)

@[simp]
lemma rTensor'_restrictScalars :
    (e.rTensor' P).restrictScalars R = (e.restrictScalars R).rTensor P := rfl

@[simp]
lemma rTensor'_apply (mp : M ⊗[R] P) :
    e.rTensor' P mp = (e.restrictScalars R).rTensor P mp := rfl

@[simp]
lemma rTensor'_coe : ⇑(e.rTensor' P) = (e.restrictScalars R).rTensor P := rfl

end LinearEquiv

