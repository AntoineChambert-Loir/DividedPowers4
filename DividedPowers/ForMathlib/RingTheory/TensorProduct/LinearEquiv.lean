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

variable {R : Type u} {M : Type v} {N : Type w}
  [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Module

open TensorProduct LinearMap

variable [AddCommMonoid N] [Module R N]

/-- Tensor a linear equivalence to the right gives a linear equivalence -/
noncomputable def LinearEquiv.rTensor
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[R] N) :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := congr e (refl R P)

/-- Tensor a linear equivalence to the left gives a linear equivalence -/
noncomputable def LinearEquiv.lTensor
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[R] N) :
    P ⊗[R] M ≃ₗ[R] P ⊗[R] N := congr (refl R P) e

variable [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]

/--  If `e` is `S`-linear, then `TensorProduct.map e f` is `S`-linear -/
noncomputable def TensorProduct.map' (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    M ⊗[R] P →ₗ[S] N ⊗[R] Q where
  toFun := map (e.restrictScalars R) f
  map_add' := map_add _
  map_smul' := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp only [hx, hy]
    | tmul m p =>
      rw [smul_tmul']
      simp only [map_tmul, coe_restrictScalars, map_smul]
      rfl

theorem TensorProduct.map'_restrictScalars (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    (map' e f).restrictScalars R = map (e.restrictScalars R) f := rfl

theorem TensorProduct.map'_coe (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    ⇑(map' e f) = ⇑(map (e.restrictScalars R) f) := rfl

/--  If `e` is a `S`-linear equivalence and `f` is an `R`-linear equivalence,
  then `TensorProduct.congr' e f` is a `S`-linear equivalence -/
noncomputable def TensorProduct.congr'
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) : M ⊗[R] P ≃ₗ[S] N ⊗[R] Q :=
  LinearEquiv.ofLinear (map' e f) (map' e.symm.toLinearMap f.symm)
    (by ext n q; simp [Function.comp_apply, map'_coe])
    (by ext m p; simp [Function.comp_apply, map'_coe])

theorem TensorProduct.congr'_restrictScalars (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    (congr' e f).restrictScalars R = (congr (e.restrictScalars R) f) := rfl

theorem TensorProduct.congr'_coe (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    ⇑(congr' e f) = ⇑(congr (e.restrictScalars R) f) := by
  rfl

/-
lemma TensorProduct.map_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (e.restrictScalars R) f) where
  map_add := LinearMap.map_add _
  map_smul := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp only [hx, hy]
    | tmul m p =>
      rw [smul_tmul']
      simp only [map_tmul, coe_restrictScalars, map_smul]
      rfl
-/

/- lemma TensorProduct.congr_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    IsLinearMap S (TensorProduct.congr (e.restrictScalars R) f) :=
  TensorProduct.map_isLinearMap' e.toLinearMap f.toLinearMap -/

/-
lemma LinearEquiv.rTensor_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    IsLinearMap S (LinearEquiv.rTensor P (e.restrictScalars R)) :=
  TensorProduct.map_isLinearMap' e.toLinearMap _
-/

variable (P : Type*) [AddCommMonoid P] [Module R P]
variable (e : M ≃ₗ[S] N)

/-- Tensor a linear equivalence to the right or to the left gives a linear equivalence-/
noncomputable def LinearEquiv.rTensor' :
    M ⊗[R] P ≃ₗ[S] N ⊗[R] P :=
  congr' e (LinearEquiv.refl R P)

lemma LinearEquiv.rTensor'_restrictScalars :
    (e.rTensor' P).restrictScalars R = (e.restrictScalars R).rTensor P :=
  rfl

lemma LinearEquiv.rTensor'_apply (mp : M ⊗[R] P) :
    e.rTensor' P mp = (e.restrictScalars R).rTensor P mp :=
  rfl

lemma LinearEquiv.rTensor'_coe (e : M ≃ₗ[S] N) :
    ⇑(e.rTensor' P) = (e.restrictScalars R).rTensor P := rfl
