/- antidiagonal with values in more general types
 inspired by a file of Bhavik Mehta
! This file was ported from Lean 3 source module antidiagonal
-/
import Mathlib.Data.Finset.PiAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Order

open scoped BigOperators

open Finset

variable {σ : Type _} [DecidableEq σ] [DecidableEq (ι → σ →₀ ℕ)]

variable {α : Type _} [CommSemiring α]

namespace MvPowerSeries

open Finset

variable [DecidableEq (ℕ → σ →₀ ℕ)]

/-- The `d`th coefficient of a finite product over `s` of power series
is the sum of products of coefficients indexed by `cut s d` -/
theorem coeff_pow (f : MvPowerSeries σ α) (n : ℕ) (d : σ →₀ ℕ) :
    coeff α d (f ^ n) =
      ∑ l in piAntidiagonal (Finset.range n) d, ∏ i in Finset.range n, coeff α (l i) f := by
  suffices f ^ n = (Finset.range n).prod fun _ => f by
    rw [this, coeff_prod]
  rw [Finset.prod_const, card_range]

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, proposition 3 -/
theorem coeff_eq_zero_of_constantCoeff_nilpotent (f : MvPowerSeries σ α) (m : ℕ)
    (hf : constantCoeff σ α f ^ m = 0) (d : σ →₀ ℕ) (n : ℕ) (hn : m + degree d ≤ n) :
    coeff α d (f ^ n) = 0 := by
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_piAntidiagonal'] at hk
  let s := (range n).filter fun i => k i = 0
  suffices hs : s ⊆ range n by
    rw [← prod_sdiff hs]
    refine' mul_eq_zero_of_right _ _
    have hs' : ∀ i ∈ s, coeff α (k i) f = constantCoeff σ α f := by
      simp only [mem_filter]
      intro i hi
      rw [hi.2, coeff_zero_eq_constantCoeff]
    rw [prod_congr rfl hs', prod_const]
    suffices m ≤ s.card by
      obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le this
      rw [hm', pow_add, hf, MulZeroClass.zero_mul]
    rw [← Nat.add_le_add_iff_right, add_comm s.card, Finset.card_sdiff_add_card_eq_card hs]
    simp only [card_range]
    apply le_trans _ hn
    simp only [add_comm m, Nat.add_le_add_iff_right]
    rw [← hk.2, map_sum, ← sum_sdiff hs]
    have hs'' : ∀ i ∈ s, degree (k i) = 0 := by
      simp only [mem_filter]
      intro i hi
      rw [hi.2, map_zero]
    rw [sum_eq_zero hs'', add_zero]
    convert Finset.card_nsmul_le_sum (range n \ s) _ 1 _
    simp only [Algebra.id.smul_eq_mul, mul_one]
    · simp only [mem_filter, mem_sdiff, mem_range, not_and, and_imp]
      intro i hi hi'; rw [← not_lt]; intro h; apply hi' hi
      simpa only [Nat.lt_one_iff, degree_eq_zero_iff] using h
  apply filter_subset


end MvPowerSeries
