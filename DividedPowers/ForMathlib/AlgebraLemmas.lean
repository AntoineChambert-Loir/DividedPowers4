import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Prime.Basic

section Factorial

open Nat

variable {A : Type*} [CommSemiring A] {I : Ideal A}

theorem natCast_factorial_isUnit_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A))
    {m : ℕ} (hmn : m < n) : IsUnit (m ! : A) := by
  apply isUnit_of_dvd_unit _ hn_fac
  apply Nat.cast_dvd_cast
  apply Nat.factorial_dvd_factorial
  exact Nat.le_sub_one_of_lt hmn

theorem natCast_factorial_isUnit_of_le {n : ℕ} (hn_fac : IsUnit (n ! : A))
    {m : ℕ} (hmn : m ≤ n) : IsUnit (m ! : A) := by
  apply isUnit_of_dvd_unit _ hn_fac
  apply Nat.cast_dvd_cast
  apply Nat.factorial_dvd_factorial
  exact hmn

theorem natCast_factorial_isUnit_of_ratAlgebra [Algebra ℚ A] (n : ℕ) :
    IsUnit (n ! : A) := by
  rw [← map_natCast (algebraMap ℚ A)]
  apply IsUnit.map
  simp [isUnit_iff_ne_zero, n.factorial_ne_zero]

theorem natCast_factorial_isUnit_of_charP {A : Type*} [CommRing A]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP A p] 
    {n : ℕ} (h : n < p) : IsUnit (n ! : A) := by 
  induction n with 
  | zero => simp
  | succ n ih => 
    simp only [factorial_succ, cast_mul, IsUnit.mul_iff]
    constructor
    · have := Int.cast_one (R := A)
      rw [← Nat.cast_one,
        ←  coprime_of_lt_prime (zero_lt_succ n) h (Fact.elim inferInstance),
        Nat.gcd_eq_gcd_ab] at this
      rw [Int.cast_add] at this
      simp only [succ_eq_add_one, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul, zero_add] at this
      exact isUnit_of_mul_eq_one _ _ this
    · exact ih (lt_trans (lt_add_one n) h )

end Factorial

section Inverse

namespace Ring

theorem inverse_pow_mul_eq_iff_eq_mul {M₀ : Type*} [CommMonoidWithZero M₀] {a : M₀} (b c : M₀)
    (ha : IsUnit a) {k : ℕ} :
  Ring.inverse a ^ k * b = c ↔ b = a ^ k * c := by
  rw [Ring.inverse_pow, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

end Ring

end Inverse

theorem Ideal.mem_pow_eq_zero {A : Type*} [CommSemiring A] {I : Ideal A} {n m : ℕ}
    (hnI : I ^ n = 0) (hmn : n ≤ m) {x : A} (hx : x ∈ I) :
    x ^ m = 0 := by
  have hxn : x ^ n = 0 := by
    rw [Ideal.zero_eq_bot] at hnI
    rw [← Ideal.mem_bot, ← hnI]
    exact Ideal.pow_mem_pow hx n
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hmn
  rw [hc, pow_add, hxn, MulZeroClass.zero_mul]
