import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Invertibility of factorials

This file contains lemmas providing sufficient conditions for the cast of `n!` to a ring `A` in
which a prime number `p` is nilpotent to be a unit.

-/

section Factorial

open Nat

variable {A : Type*} [CommRing A]

lemma IsUnit.natCast_of_lt_of_isNilpotent {p n : ℕ} [Fact (Nat.Prime p)] (hp : IsNilpotent (p : A))
    (h₀ : n ≠ 0) (h : n < p) : IsUnit (n : A) := by
  obtain ⟨m, hm⟩ := hp
  have : Coprime (p ^ m) n := by
    apply Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.elim (inferInstance))]
    exact Nat.not_dvd_of_pos_of_lt (zero_lt_of_ne_zero h₀) h
  suffices ∃ (a b : A), p ^ m * a + n * b = 1 by
    obtain ⟨a, b, h⟩ := this
    rw [hm, zero_mul, zero_add] at h
    exact isUnit_iff_exists.mpr ⟨b, by rw [h, mul_comm, h, and_self]⟩
  have hcoe : ((p ^ m).gcd n : A) = (((p ^ m).gcd n : ℤ) : A) := by rw [Int.cast_natCast]
  rw [← Nat.cast_one, ← this]
  exact ⟨(p ^ m).gcdA (n), (p ^ m).gcdB n, by norm_cast; rw [hcoe, Nat.gcd_eq_gcd_ab (p^m) n]⟩

theorem IsUnit.natCast_factorial_of_isNilpotent {p : ℕ} [Fact (Nat.Prime p)]
    (hp : IsNilpotent (p : A)) {n : ℕ} (h : n < p) : IsUnit (n ! : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    exact ⟨IsUnit.natCast_of_lt_of_isNilpotent hp (succ_ne_zero n) h,
      ih (lt_trans (lt_add_one n) h)⟩

end Factorial
