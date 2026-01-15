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

-- TODO: PR
lemma IsFractionRing.charZero (R K : Type*) [CommRing R] [CharZero R] [CommRing K] [Algebra R K]
    [IsFractionRing R K] : CharZero K := by
  refine charZero_of_inj_zero ?_
  intro n hn
  rw [← Nat.cast_eq_zero (R := R)]
  exact IsFractionRing.injective R K (by simp [hn])

-- TODO: PR (?)
instance (R : Type*) [CommRing R] [CharZero R] : CharZero (FractionRing R) :=
  IsFractionRing.charZero R (FractionRing R)

-- TODO: PR to RatAlgebra
def _root_.RatAlgebra.dividedPowersTop {R : Type*} [CommRing R] [Algebra ℚ R]  :
    DividedPowers (⊤ : Ideal R) :=
  have : DecidablePred fun x ↦ x ∈ (⊤ : Ideal R) := by
    simp only [Submodule.mem_top]
    infer_instance --instDecidableTrue
  RatAlgebra.dividedPowers ⊤

namespace DividedPowerAlgebra

variable (ι R K : Type*) [CommRing R] [CharZero R] [CommRing K] [Algebra R K] [IsFractionRing R K]

section Polynomial

open Module Polynomial

--[Algebra ℚ (FractionRing R)] -- [IsDomain R]

-- [Algebra ℚ (FractionRing R)] should be enough (instead of IsDomain R),
-- but Algebra ℚ (FractionRing ℤ) is not found

def expPolynomial [Algebra ℚ K] : Subalgebra R K[X] :=
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

namespace Int

variable {M : Type*} [AddCommGroup M] {ι : Type*} [Unique ι] (b : Basis ι ℤ M)

--TODO: rename
def morphism : DividedPowerAlgebra ℤ M →ₐ[ℤ] ℚ[X] :=
  DividedPowerAlgebra.lift RatAlgebra.dividedPowersTop (b.constr ℤ fun _ ↦ (X : ℚ[X])) (by simp)

lemma injective_morphism : Function.Injective (morphism b) := sorry

lemma range_morphism : AlgHom.range (morphism b) = expPolynomial ℤ ℚ := sorry

end Int

variable {R} {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Unique ι] (b : Basis ι R M)
  [Algebra ℚ K] -- Should this already exist as a definition or as an instance?

--TODO: rename
def morphism : DividedPowerAlgebra R M →ₐ[R] K[X] :=
  DividedPowerAlgebra.lift RatAlgebra.dividedPowersTop (b.constr R fun _ ↦ (X : K[X])) (by simp)

lemma injective_morphism : Function.Injective (morphism K b) := sorry

lemma range_morphism : AlgHom.range (morphism K b) = expPolynomial R K := sorry

end Polynomial

section MvPolynomial

open Module MvPolynomial

--[Algebra ℚ (FractionRing R)] -- [IsDomain R]

-- [Algebra ℚ (FractionRing R)] should be enough (instead of IsDomain R),
-- but Algebra ℚ (FractionRing ℤ) is not found

variable [Algebra ℚ K]

variable {ι} in
def dpowMonomial (n : ι →₀ ℕ) (r : R) : MvPolynomial ι K :=
  r • n.prod fun i k ↦ (1/(k.factorial : ℚ)) • (X i : MvPolynomial ι K)^k

section Finset

theorem smul_prod {ι M N : Type*}
    [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : M) (f : ι → N) :
    b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x := by
  have : Multiset.map (fun (x : ι) ↦ b • f x) s.val =
      Multiset.map (fun x ↦ b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]

theorem prod_smul {ι M N : Type*}
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : ι → M) (f : ι → N) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

end Finset

--TODO: golf
omit [CharZero R] [IsFractionRing R K] in
lemma dpowMonomial_linearIndependent [Nontrivial K] [IsDomain R] [IsTorsionFree R K] :
    LinearIndependent R (fun (n : ι →₀ ℕ) ↦ dpowMonomial R K n 1) := by
  classical
  rw [LinearIndependent, ← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  simp only [dpowMonomial, one_div, one_smul, LinearMap.mem_ker] at hx
  ext n
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  have := congr(coeff n $hx)
  simp only [coeff_zero] at this
  rw [Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum, Finset.sum_eq_single n] at this
  · rw [coeff_smul, ← smul_zero (x n)] at this
    by_contra h0
    -- Refine next step to remove `IsDomain R`, `IsTorsionFree R K`.
    -- Possible because of `Algebra ℚ K` plus product of factorials is a unit.
    rw [smul_right_inj h0] at this
    rw [Finsupp.prod, prod_smul, coeff_smul] at this
    simp only [prod_inv_distrib, prod_X_pow_eq_monomial, smul_eq_zero, inv_eq_zero] at this
    simp only [coeff_monomial, ↓reduceIte, one_ne_zero, or_false] at this
    rw [Finset.prod_eq_zero_iff] at this
    obtain ⟨a, _, ha⟩ := this
    norm_cast at ha
    apply Nat.factorial_ne_zero (n a) ha
  · intro b hb hbn
    simp only [coeff_smul, smul_eq_zero]
    aesop (add norm [Finsupp.prod, prod_smul])
  · intro hn
    aesop

def expMvPolynomial : Subalgebra R (MvPolynomial ι K) :=
  { carrier := Submodule.span R
      (Set.range (fun (n : ι →₀ ℕ) ↦ dpowMonomial R K n 1))
    mul_mem' {p} {q} hp hq := by
      induction hp using Submodule.span_induction generalizing q with
      | @mem p hp =>
        obtain ⟨m, rfl⟩ := hp
        induction hq using Submodule.span_induction with
        | @mem q hq => sorry
        | zero => sorry
        | add => sorry
        | smul => sorry
      | zero => sorry
      | add => sorry
      | smul => sorry
    one_mem' := Submodule.mem_span_of_mem ⟨0, by simp [dpowMonomial]⟩
    add_mem' {p} {q} hp hq := Submodule.add_mem _ hp hq
    zero_mem' := by simp
    algebraMap_mem' r := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_of_mem ⟨0, by simp [dpowMonomial]⟩)}

def expBasis [Nontrivial K] [IsDomain R] [IsTorsionFree R K] :
    Basis (ι →₀ ℕ) R (expMvPolynomial ι R K) :=
  Module.Basis.span (dpowMonomial_linearIndependent ι R K)

variable {ι} {R} {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
   [Nontrivial K] [IsDomain R] [IsTorsionFree R K]

--TODO: rename
def mvMorphism : DividedPowerAlgebra R M →ₐ[R] MvPolynomial ι K :=
  DividedPowerAlgebra.lift RatAlgebra.dividedPowersTop
    (b.constr ℤ fun i ↦ (X i : MvPolynomial ι K)) (by simp)

def mvMorphismInv : expMvPolynomial ι R K →ₗ[R] DividedPowerAlgebra R M :=
  (expBasis ι R K).constr R fun n ↦  n.prod (fun i k ↦ dp R k (b i))

#check ((mvMorphism K b).toLinearMap.comp (mvMorphismInv K b))

lemma mvMorphism_comp_eq_id :
    ((mvMorphism K b).toLinearMap.comp (mvMorphismInv K b)) =
      (expMvPolynomial ι R K).val := by
  apply (expBasis ι R K).ext
  intro n
  simp only [LinearMap.coe_comp, AlgHom.coe_toLinearMap, Function.comp_apply,
    AlgHom.linearMapMk_toAddHom, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
    expBasis]
  erw [Basis.span_apply (dpowMonomial_linearIndependent ι R K) n] --Why erw?
  simp only [mvMorphismInv,]
  rw [Basis.constr_apply]

  sorry

lemma range_mvMorphism : AlgHom.range (mvMorphism K b) = expMvPolynomial ι R K := sorry

lemma injective_mvMorphism : Function.Injective (mvMorphism K b) := sorry


end MvPolynomial
