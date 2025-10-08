/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DividedPowers.Basic

/-! # Divided powers

We provide some additional formulas for computation with divided powers.

## Main results

* `DividedPowers.dpow_linearCombination`: ` "multinomial" theorem for divided powers, without
  multinomial coefficients

* `DividedPowers.dpow_prod`: given a nonempty `s : Finset ι` and a family `r : ι → R` such that
  `r i ∈ I` for all `i ∈ S`, then for all `n : ℕ`, one has
  `hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i))`.
-/

namespace DividedPowers

open Finset

variable {R : Type*} [CommSemiring R] {I : Ideal R} (hI : DividedPowers I)
  {ι : Type*} [DecidableEq ι]

/-- A "multinomial" theorem for divided powers — without multinomial coefficients -/
theorem dpow_finsupp_sum {x : ι →₀ R} (hx : ∀ i, x i ∈ I) {n : ℕ} :
    hI.dpow n (x.sum fun _ r ↦ r) =
      ∑ k ∈ (x.support.sym n), x.prod fun i r ↦ hI.dpow (Multiset.count i k) r := by
  simp [Finsupp.sum, hI.dpow_sum (fun i _ ↦ hx i), Finsupp.prod]

/-- A "multinomial" theorem for divided powers — without multinomial coefficients -/
theorem dpow_linearCombination {A : Type*} [CommSemiring A] [Algebra R A] {J : Ideal A}
    (hJ : DividedPowers J) {b : ι → A} {x : ι →₀ R} (hx : ∀ i ∈ x.support, b i ∈ J) {n : ℕ} :
    hJ.dpow n (x.sum fun i r ↦ r • (b i)) =
      ∑ k ∈ x.support.sym n,
        x.prod fun i r ↦ r ^ (Multiset.count i k) • hJ.dpow (Multiset.count i k) (b i) := by
  rw [Finsupp.sum, hJ.dpow_sum (fun i hi ↦ Submodule.smul_of_tower_mem J _ (hx i hi))]
  apply Finset.sum_congr rfl
  intros
  simp only [Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Algebra.smul_def, hJ.dpow_mul (hx i hi), ← map_pow, ← Algebra.smul_def]

/-- Given a nonempty `s : Finset ι` and a family `r : ι → R` such that `r i ∈ I` for all `i ∈ S`,
  one has `hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i))`
  for all `n : ℕ`. -/
theorem dpow_prod {r : ι → R} {s : Finset ι} (hs : s.Nonempty) (hs' : ∀ i ∈ s, r i ∈ I) {n : ℕ} :
    hI.dpow n (∏ i ∈ s, r i) = n.factorial ^ (s.card - 1) • (∏ i ∈ s, hI.dpow n (r i)) := by
  induction s using Finset.induction with
  | empty => simp_all
  | @insert a s has hrec =>
    rw [Finset.prod_insert has]
    by_cases h : s.Nonempty
    · rw [dpow_mul]
      · simp only [Finset.card_insert_of_notMem has, add_tsub_cancel_right,
          nsmul_eq_mul, Nat.cast_pow, Finset.prod_insert has]
        rw [hrec h]
        · simp only [nsmul_eq_mul, Nat.cast_pow, ← mul_assoc]
          apply congr_arg₂ _ _ rfl
          have : #s = #s - 1 + 1 := by
            refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
            exact one_le_card.mpr h
          nth_rewrite 2 [this]
          rw [mul_comm, pow_succ, mul_assoc, hI.factorial_mul_dpow_eq_pow]
          exact hs' a (mem_insert_self a s)
        · intro i hi
          apply hs' i (mem_insert_of_mem hi)
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_prod_diff_singleton_mul hj]
      apply Ideal.mul_mem_left
      apply hs' j (mem_insert_of_mem hj)
    · simp only [not_nonempty_iff_eq_empty] at h
      simp [h]

end DividedPowers
