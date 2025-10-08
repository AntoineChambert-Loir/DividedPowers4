/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic

open TensorProduct

theorem LinearEquiv.rTensor_apply {R : Type*} [CommSemiring R] (M : Type*) {N P : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    (f : N ≃ₗ[R] P) (nm : N ⊗[R] M) :
    LinearEquiv.rTensor M f nm = (f : N →ₗ[R] P).rTensor M nm := rfl
