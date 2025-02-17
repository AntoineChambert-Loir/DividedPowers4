/-
Copyright (c) 2022 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.Basic
import DividedPowers.ForMathlib.AlgebraLemmas

open Nat

section NatLemmas

open Ring

lemma Nat.isUnitFactorial (n : ℕ) : IsUnit (n ! : ℚ) := by
  simp only [isUnit_iff_ne_zero, ne_eq, cast_eq_zero, factorial_ne_zero, not_false_eq_true]

lemma Nat.inv_smul_eq_invCast_mul {A : Type*} [CommSemiring A] [Algebra ℚ A] {n : ℕ} {a : A} :
    inverse (n : ℚ) • a = inverse (n : A) * a := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp only [hn, Nat.cast_zero, isUnit_zero_iff, not_false_eq_true, inverse_non_unit,
      zero_smul, inverse_zero, zero_mul]
  · suffices hn' : IsUnit (n : ℚ) by
      rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ A), eq_comm,
        inverse_mul_eq_iff_eq_mul _ _ _ (RingHom.isUnit_map _ hn'), ← mul_assoc, eq_comm]
      convert @one_mul A _ _
      rw [← map_mul, ← map_one (algebraMap ℚ A)]
      apply congr_arg
      rw [eq_comm, eq_mul_inverse_iff_mul_eq _ _ _ hn', one_mul]
    simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
    exact Nat.ne_of_gt hn

lemma Nat.castChoose_eq {A : Type*} [CommSemiring A] {m : ℕ} {k : ℕ × ℕ}
    (hm : IsUnit (m ! : A)) (hk : k ∈ Finset.antidiagonal m) :
    (choose m k.1 : A) = ↑m ! * inverse ↑k.1! * inverse ↑k.2! := by
  rw [Finset.mem_antidiagonal] at hk
  rw [eq_mul_inverse_iff_mul_eq, eq_mul_inverse_iff_mul_eq,
    ← hk, ← Nat.cast_mul, ← Nat.cast_mul, add_comm, Nat.add_choose_mul_factorial_mul_factorial] <;>
  apply natCast_factorial_isUnit_of_le hm <;>
  rw [← hk];
  exacts [Nat.le_add_right k.1 k.2, Nat.le_add_left k.2 k.1]

end NatLemmas

open Ring

namespace DividedPowers

namespace OfInvertibleFactorial

variable {A : Type*} [CommSemiring A] (I : Ideal A) [DecidablePred (fun x ↦ x ∈ I)]

/-- The family of functions `ℕ → I → I` given by `x^n/n!`. -/
noncomputable def dpow : ℕ → A → A := fun m x => if x ∈ I then inverse (m ! : A) * x ^ m else 0

variable {I}

theorem dpow_eq_of_mem {m : ℕ} {x : A} (hx : x ∈ I) : dpow I m x = inverse (m ! : A) * x ^ m := by
  simp only [dpow, if_pos hx]

theorem dpow_eq_of_not_mem {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by
  simp only [dpow, if_neg hx]

theorem dpow_null {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by
  simp only [dpow, if_neg hx]

theorem dpow_zero {x : A} (hx : x ∈ I) : dpow I 0 x = 1 := by
  simp only [dpow, factorial_zero, cast_one, inverse_one, _root_.pow_zero, mul_one, if_pos hx]

theorem dpow_one {x : A} (hx : x ∈ I) : dpow I 1 x = x := by
  rw [dpow_eq_of_mem hx, pow_one, Nat.factorial_one, Nat.cast_one, inverse_one, one_mul]

theorem dpow_mem {m : ℕ} (hm : m ≠ 0) {x : A} (hx : x ∈ I) : dpow I m x ∈ I := by
  rw [dpow_eq_of_mem hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))

theorem dpow_add_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1) ! : A)) {m : ℕ} (hmn : m < n)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum (fun k ↦ dpow I k.1 x * dpow I k.2 y) := by
  rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [inverse_mul_eq_iff_eq_mul _ _ _ (natCast_factorial_isUnit_of_lt hn_fac hmn),
    Finset.mul_sum, Commute.add_pow' (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos hx, if_pos hy]
  ring_nf
  simp only [mul_assoc]; congr; rw [← mul_assoc]
  exact castChoose_eq (natCast_factorial_isUnit_of_lt hn_fac hmn) hk

theorem dpow_add {n : ℕ} (hn_fac : IsUnit ((n - 1) ! : A)) (hnI : I ^ n = 0) {m : ℕ} {x : A}
    (hx : x ∈ I) {y : A} (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.antidiagonal m).sum fun k ↦ dpow I k.1 x * dpow I k.2 y := by
  by_cases hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · have h_sub : I ^ m ≤ I ^ n := Ideal.pow_le_pow_right (not_lt.mp hmn)
    rw [dpow_eq_of_mem (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 := by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
      exact Set.mem_of_subset_of_mem h_sub (Ideal.pow_mem_pow (Ideal.add_mem I hx hy) m)
    rw [hxy, mul_zero, eq_comm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_pos hx, if_pos hy, mul_assoc, mul_comm (x ^ k.1), mul_assoc, ← mul_assoc]
    apply mul_eq_zero_of_right
    rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
    apply Set.mem_of_subset_of_mem h_sub
    rw [← Finset.mem_antidiagonal.mp hk, add_comm, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hy _) (Ideal.pow_mem_pow hx _)

theorem dpow_smul {m : ℕ} {a x : A} (hx : x ∈ I) : dpow I m (a * x) = a ^ m * dpow I m x := by
  rw [dpow_eq_of_mem (Ideal.mul_mem_left I _ hx), dpow_eq_of_mem hx,
    mul_pow, ← mul_assoc, mul_comm _ (a ^ m), mul_assoc]

theorem dpow_mul_of_add_lt {n : ℕ} (hn_fac : IsUnit ((n - 1) ! : A)) {m k : ℕ}
    (hkm : m + k < n) {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hx, dpow_eq_of_mem hx, dpow_eq_of_mem hx,
    mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m),
    ← pow_add, ← mul_assoc, ← mul_assoc]
  apply congr_arg₂ _ _ rfl
  rw [eq_mul_inverse_iff_mul_eq _ _ _ (natCast_factorial_isUnit_of_lt hn_fac hkm),
      mul_assoc,
      inverse_mul_eq_iff_eq_mul _ _ _ (natCast_factorial_isUnit_of_lt hn_fac hm),
      inverse_mul_eq_iff_eq_mul _ _ _ (natCast_factorial_isUnit_of_lt hn_fac hk)]
  norm_cast; apply congr_arg
  rw [← Nat.add_choose_mul_factorial_mul_factorial, mul_comm, mul_comm _ (m !), Nat.choose_symm_add]

theorem dpow_mul {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x := by
  by_cases hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.mem_pow_eq_zero hnI (not_lt.mp hkm) hx
    rw [dpow_eq_of_mem hx, dpow_eq_of_mem hx, dpow_eq_of_mem hx,
      mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m), ← pow_add, hxmk,
      mul_zero, mul_zero, mul_zero, mul_zero]

theorem dpow_comp_of_mul_lt {n : ℕ} (hn_fac : IsUnit ((n - 1) ! : A)) {m k : ℕ} (hk : k ≠ 0)
    (hkm : m * k < n) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m := m * k) hx, dpow_eq_of_mem (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero, cast_one, one_mul]
  · have hkn : k < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)) hkm
    rw [dpow_eq_of_mem hx, mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [eq_mul_inverse_iff_mul_eq _ _ _ (natCast_factorial_isUnit_of_lt hn_fac hkm),
      mul_assoc, inverse_mul_eq_iff_eq_mul _ _ _ (natCast_factorial_isUnit_of_lt hn_fac hmn),
      inverse_pow_mul_eq_iff_eq_mul _ _ (natCast_factorial_isUnit_of_lt hn_fac hkn),
      ← uniformBell_mul_eq _ hk]
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring_nf

theorem dpow_comp {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(uniformBell m k) * dpow I (m * k) x := by
  by_cases hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.mem_pow_eq_zero hnI (not_lt.mp hmk) hx
    rw [dpow_eq_of_mem (dpow_mem hk hx), dpow_eq_of_mem hx, dpow_eq_of_mem hx,
      mul_pow, ← pow_mul, ← mul_assoc, mul_comm k, hxmk, mul_zero, mul_zero, mul_zero]

/-- If `(n-1)!` is invertible in `A` and `I^n = 0`, then `I` admits a divided power structure.
  Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def dividedPowers {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A))
    (hnI : I ^ n = 0) : DividedPowers I where
  dpow             := dpow I
  dpow_null _ _ hx := dpow_null hx
  dpow_zero hx     := dpow_zero hx
  dpow_one hx      := dpow_one hx
  dpow_mem _ _ hn hx    := dpow_mem hn hx
  dpow_add _ _ _ hx hy  := dpow_add hn_fac hnI hx hy
  dpow_smul _ _ _ hx    := dpow_smul hx
  dpow_mul _ _ _ hx     := dpow_mul hn_fac hnI hx
  dpow_comp _ _ _ hk hx := dpow_comp hn_fac hnI hk hx

lemma dpow_apply {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) {m : ℕ} {x : A} :
    (dividedPowers (hn_fac) (hnI)).dpow m x =
      if x ∈ I then inverse (m.factorial : A) * x ^ m else 0 := rfl

end OfInvertibleFactorial

namespace OfSquareZero

variable {A : Type*} [CommSemiring A] {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)]
  (hI2 : I ^ 2 = 0)

/-- If `I^2 = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (by norm_num) hI2

theorem dpow_of_two_le {n : ℕ} (hn : 2 ≤ n) (a : A) :
    (dividedPowers hI2) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.mem_pow_eq_zero hI2 hn ha, mul_zero]

end OfSquareZero

namespace CharP

variable {A : Type*} [CommRing A] {p : ℕ} [Fact (Nat.Prime p)] [CharP A p]
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (n := p)
    (natCast_factorial_isUnit_of_charP p (Nat.sub_one_lt (NeZero.ne' p).symm))
    hIp

theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers hIp) n a = 0 := by
  simp only [dividedPowers, OfInvertibleFactorial.dpow_apply, ite_eq_right_iff]
  intro ha
  rw [Ideal.mem_pow_eq_zero hIp hn ha, mul_zero]

end CharP

-- We formalize example 2 from [BO], Section 3.
namespace RatAlgebra

variable {R : Type*} [CommSemiring R] (I : Ideal R) [DecidablePred (fun x ↦ x ∈ I)]

/-- The family `ℕ → R → R` given by `dpow n x = x ^ n / n!`. -/
noncomputable def dpow : ℕ → R → R := OfInvertibleFactorial.dpow I

variable {I}

theorem dpow_eq_of_mem (n : ℕ) {x : R} (hx : x ∈ I) :
    dpow I n x = (inverse n.factorial : R) * x ^ n := by
  rw [dpow, OfInvertibleFactorial.dpow_eq_of_mem hx]

variable [Algebra ℚ R]

variable (I)

/-- If `I` is an ideal in a `ℚ`-algebra `A`, then `I` admits a unique divided power structure,
  given by `dpow n x = x ^ n / n!`. -/
noncomputable def dividedPowers : DividedPowers I where
  dpow           := dpow I
  dpow_null _ _ hx   := OfInvertibleFactorial.dpow_null hx
  dpow_zero hx   := OfInvertibleFactorial.dpow_zero hx
  dpow_one hx    := OfInvertibleFactorial.dpow_one hx
  dpow_mem _ _ hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add n _ _ hx hy := OfInvertibleFactorial.dpow_add_of_lt
    (natCast_factorial_isUnit_of_ratAlgebra _) (n.lt_succ_self) hx hy
  dpow_smul _ _ _ hx := OfInvertibleFactorial.dpow_smul hx
  dpow_mul {m} k _ hx := OfInvertibleFactorial.dpow_mul_of_add_lt
    (natCast_factorial_isUnit_of_ratAlgebra _) (m + k).lt_succ_self hx
  dpow_comp _ _ _ hk hx := OfInvertibleFactorial.dpow_comp_of_mul_lt
    (natCast_factorial_isUnit_of_ratAlgebra _) hk (lt_add_one _) hx

@[simp]
lemma dpow_apply {n : ℕ} {x : R} :
    (dividedPowers I).dpow n x = if x ∈ I then inverse (n.factorial : R) * x ^ n else 0 := rfl

omit [DecidablePred fun x ↦ x ∈ I] in
/-- If `I` is an ideal in a `ℚ`-algebra `A`, then the divided power structure on `I` given by
  `dpow n x = x ^ n / n!` is the only possible one. -/
theorem dpow_eq_inv_fact_smul (hI : DividedPowers I) {n : ℕ} {x : R} (hx : x ∈ I) :
    hI.dpow n x = (inverse (n.factorial : ℚ)) • x ^ n := by
  rw [inverse_eq_inv', ← factorial_mul_dpow_eq_pow hI hx, ← smul_eq_mul, ← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : ℚ) • (1 : R) := by
    rw [cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [aux, ← mul_smul]
  suffices (n ! : ℚ)⁻¹ * (n !) = 1 by
    rw [this, one_smul]
  apply Rat.inv_mul_cancel
  rw [← cast_zero, ne_eq]
  simp [cast_zero, cast_eq_zero,factorial_ne_zero, not_false]

variable {I}

/-- There are no other divided power structures on a `ℚ`-algebra. -/
theorem dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I :=
  hI.eq_of_eq_on_ideal _ (fun n x hx ↦
    by rw [dpow_apply, if_pos hx, eq_comm, inverse_mul_eq_iff_eq_mul _ _ _
      (natCast_factorial_isUnit_of_ratAlgebra n), factorial_mul_dpow_eq_pow _ hx])

end RatAlgebra

end DividedPowers
