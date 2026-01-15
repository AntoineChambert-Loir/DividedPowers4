/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.BaseChange
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.ForMathlib.RingTheory.TensorProduct.DirectLimit.FG
import DividedPowers.ForMathlib.Data.FinsetLemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import DividedPowers.ForMathlib.RingTheory.DividedPowers.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Algebra.Rat
--import Mathlib.FieldTheory.RatFunc.Defs

noncomputable section

open DividedPowers Finset --Ideal Ideal.Quotient --MvPolynomial RingQuot

namespace DividedPowerAlgebra

section Polynomial

open Module Polynomial

-- TODO: PR
instance (R : Type*) [CommRing R] [CharZero R] : CharZero (FractionRing R) := by
  refine charZero_of_inj_zero ?_
  intro n hn
  rw [← Nat.cast_eq_zero (R := R)]
  exact IsFractionRing.injective R (FractionRing R) (by simp [hn])

variable (R : Type*) [CommRing R] [CharZero R] --[Algebra ℚ (FractionRing R)] -- [IsDomain R]

-- [Algebra ℚ (FractionRing R)] should be enough (instead of IsDomain R),
-- but Algebra ℚ (FractionRing ℤ) is not found

def expPolynomial [Algebra ℚ (FractionRing R)] : Subalgebra R (FractionRing R)[X] :=
  let K := FractionRing R
  { carrier := Submodule.span R
      (Set.range (fun (n : ℕ) ↦ (1/(Nat.factorial n : ℚ)) • (X : K[X])^n))
    mul_mem' {p} {q} hp hq := by
      induction hp using Submodule.span_induction generalizing q with
      | @mem p hp =>
        obtain ⟨m, rfl⟩ := hp
        induction hq using Submodule.span_induction with
        | @mem q hq =>
          obtain ⟨n, rfl⟩ := hq
          simp only
          have : (1 / (m.factorial : ℚ)) • (X : K[X]) ^ m * (1 / (n.factorial : ℚ)) •
              (X : K[X]) ^ n =
              (Nat.choose (m + n) m) • (1/((m + n).factorial : ℚ)) • (X : K[X]) ^ (m + n) := by
            rw [smul_mul_smul]
            simp only [← pow_add, ← IsScalarTower.smul_assoc]
            congr 1
            rw [add_comm m n, Nat.add_choose n m]
            simp only [one_div, nsmul_eq_mul]
            field_simp
            norm_cast
            rw [mul_comm m.factorial, Nat.mul_div_cancel' (Nat.factorial_mul_factorial_dvd_factorial_add n m)]
          rw [this]
          apply Submodule.smul_of_tower_mem
          apply Submodule.mem_span_of_mem
          exact ⟨m + n, rfl⟩
        | zero => sorry
        | add => sorry
        | smul => sorry
      | zero => sorry
      | add => sorry
      | smul => sorry
    one_mem' := Submodule.mem_span_of_mem ⟨0, by simp⟩
    add_mem' {p} {q} hp hq := Submodule.add_mem _ hp hq
    zero_mem' := by simp
    algebraMap_mem' r := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_of_mem ⟨0, by simp⟩)}

/- instance : CharZero (FractionRing ℤ) := by
  refine charZero_of_inj_zero ?_
  intro n hn
  rw [← Int.ofNat_eq_zero]
  apply IsFractionRing.injective ℤ (FractionRing ℤ)
  simp [hn]
 -/

/- instance : Algebra ℚ (FractionRing ℤ) := by
  infer_instance -/

--#check expPolynomial ℤ

--#synth CharZero ℤ

variable {M : Type*} [AddCommGroup M] {ι : Type*} [Unique ι] (b : Basis ι ℤ M)

-- TODO: PR to RatAlgebra
def _root_.RatAlgebra.dividedPowersTop {R : Type*} [CommRing R] [Algebra ℚ R]  :
    DividedPowers (⊤ : Ideal R) :=
  have : DecidablePred fun x ↦ x ∈ (⊤ : Ideal R) := by
    simp only [Submodule.mem_top]
    infer_instance --instDecidableTrue
  RatAlgebra.dividedPowers ⊤

--TODO: rename
def morphism : DividedPowerAlgebra ℤ M →ₐ[ℤ] ℚ[X] :=
  DividedPowerAlgebra.lift RatAlgebra.dividedPowersTop (b.constr ℤ fun _ ↦ (X : ℚ[X])) (by simp)

lemma injective_morphism : Function.Injective (morphism b) := sorry

lemma range_morphism : AlgHom.range (morphism b) = expPolynomial := sorry
