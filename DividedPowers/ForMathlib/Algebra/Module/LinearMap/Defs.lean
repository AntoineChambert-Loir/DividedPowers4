/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Module.LinearMap.Defs

open LinearMap

@[simp]
lemma LinearMap.restrictScalars_id (R : Type*) {S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [Module S M] [CompatibleSMul M M R S] :
    (LinearMap.id (R := S) (M := M)).restrictScalars R = LinearMap.id  := rfl

@[simp]
lemma restrictScalars_self {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) : f.restrictScalars R = f := rfl
