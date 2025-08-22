import Mathlib.Algebra.Module.LinearMap.Defs

open LinearMap

@[simp]
lemma LinearMap.restrictScalars_id (R : Type*) {S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [Module S M] [CompatibleSMul M M R S] :
    (LinearMap.id (R := S) (M := M)).restrictScalars R = LinearMap.id  := rfl
