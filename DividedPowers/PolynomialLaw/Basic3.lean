/- Copyright ACL @ MIdFF 2024 -/

import DividedPowers.ForMathlib.RingTheory.TensorProduct.DirectLimit.FG
import DividedPowers.ForMathlib.RingTheory.Congruence.Hom

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Logic.Small.Set
import Mathlib.RingTheory.PolynomialLaw.Basic

import DividedPowers.PolynomialLaw.Basic2

/-! # Polynomial laws on modules

Complements that should be in `Basic`
-/

universe u v w

open scoped TensorProduct
open AlgHom LinearMap

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R]
  {M N P : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]

theorem sum_toFun' {ι : Type*} [DecidableEq ι] (f : ι → (M →ₚₗ[R] N)) (s : Finset ι)
  (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (∑ i ∈ s, f i).toFun' S m = ∑ i ∈ s, (f i).toFun' S m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his hs =>
    simp [Finset.sum_insert his, hs]

theorem sum_toFun {ι : Type*} [DecidableEq ι] (f : ι → (M →ₚₗ[R] N)) (s : Finset ι)
  (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (∑ i ∈ s, f i).toFun S m = ∑ i ∈ s, (f i).toFun S m := by
  obtain ⟨⟨t, p⟩, hm⟩ := π_surjective m
  simp [toFun_eq_toFunLifted_apply _ hm, sum_toFun']

theorem zero_comp (g : P →ₚₗ[R] M) :
    (0 : M →ₚₗ[R] N).comp g = 0 := by
  ext S _ _ p
  simp [comp_toFun']

theorem add_comp (f f' : M →ₚₗ[R] N) (g : P →ₚₗ[R] M) :
    (f + f').comp g = f.comp g + f'.comp g := by
  ext S _ _ p
  simp [comp_toFun']

theorem smul_comp (r : R) (f : M →ₚₗ[R] N) (g : P →ₚₗ[R] M) :
    (r • f).comp g = r • f.comp g := by
  ext S _ _ p
  simp [comp_toFun']

theorem sum_comp {ι : Type*} [DecidableEq ι] (f : ι → (M →ₚₗ[R] N)) (g : P →ₚₗ[R] M) (s : Finset ι) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  induction s using Finset.induction_on with
  | empty => simp [zero_comp]
  | insert i s his hs =>
    simp [Finset.sum_insert his, add_comp, hs]

#check id_comp
