import Mathlib.RingTheory.Ideal.Operations

section Induction

namespace Submodule

universe u v

variable {R : Type u} {M : Type v} {F : Type _} {G : Type _}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {I J : Ideal R} {N P Q : Submodule R M}

-- TODO : add other if needed
end Submodule

end Induction

section Factorial

variable {A : Type _} [CommSemiring A] {I : Ideal A}

theorem factorial_isUnit {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) {m : ℕ} (hmn : m < n) :
    IsUnit (m.factorial : A) := by
  apply isUnit_of_dvd_unit _ hn_fac
  apply Nat.coe_nat_dvd
  apply Nat.factorial_dvd_factorial
  exact Nat.le_sub_one_of_lt hmn
#align factorial_is_unit factorial_isUnit

theorem Factorial.isUnit [Algebra ℚ A] (n : ℕ) : IsUnit (n.factorial : A) :=
  by
  rw [← map_natCast (algebraMap ℚ A)]
  apply IsUnit.map
  rw [isUnit_iff_ne_zero]
  simp only [ne_eq, Nat.cast_eq_zero]
  exact Nat.factorial_ne_zero n
#align factorial.is_unit Factorial.isUnit

end Factorial

section Inverse

namespace Ring

theorem inverse_pow_mul_eq_iff_eq_mul {M₀ : Type _} [CommMonoidWithZero M₀] {a : M₀} (b c : M₀)
    (ha : IsUnit a) {k : ℕ} : Ring.inverse a ^ k * b = c ↔ b = a ^ k * c := by
  rw [Ring.inverse_pow, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]
#align ring.inverse_pow_mul_eq_iff_eq_mul Ring.inverse_pow_mul_eq_iff_eq_mul

end Ring

end Inverse

theorem Ideal.mem_pow_eq_zero {A : Type _} [CommSemiring A] {I : Ideal A} (n m : ℕ) (hnI : I ^ n = 0)
    (hmn : n ≤ m) {x : A} (hx : x ∈ I) : x ^ m = 0 :=
  by
  have hxn : x ^ n = 0 := by
    rw [Ideal.zero_eq_bot] at hnI
    rw [← Ideal.mem_bot, ← hnI]
    exact Ideal.pow_mem_pow hx n
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hmn
  rw [hc, pow_add, hxn, MulZeroClass.zero_mul]
#align ideal.mem_pow_eq_zero Ideal.mem_pow_eq_zero
