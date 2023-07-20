import DividedPowers.ForMathlib.AlgebraLemmas
import DividedPowers.Basic
import Mathlib.Algebra.Algebra.Basic

namespace DividedPowers

namespace OfInvertibleFactorial

variable {A : Type _} [CommRing A] {I : Ideal A}

open scoped Classical

noncomputable def dpow (I : Ideal A) : ℕ → A → A := fun m x =>
  if x ∈ I then Ring.inverse (m.factorial : A) * x ^ m else 0
#align divided_powers.of_invertible_factorial.dpow DividedPowers.OfInvertibleFactorial.dpow

theorem dpow_eq_of_mem {I : Ideal A} (m : ℕ) {x : A} (hx : x ∈ I) :
  dpow I m x = Ring.inverse (m.factorial : A) * x ^ m := by 
  simp only [dpow] ; rw [if_pos hx]
#align divided_powers.of_invertible_factorial.dpow_dif_pos DividedPowers.OfInvertibleFactorial.dpow_eq_of_mem

theorem dpow_eq_of_not_mem {I : Ideal A} {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by
  simp only [dpow] ; rw [if_neg hx]
#align divided_powers.of_invertible_factorial.dpow_dif_neg DividedPowers.OfInvertibleFactorial.dpow_eq_of_not_mem

theorem dpow_null {m : ℕ} {x : A} (hx : x ∉ I) : dpow I m x = 0 := by
  simp only [dpow] ; rw [if_neg hx]
#align divided_powers.of_invertible_factorial.dpow_null DividedPowers.OfInvertibleFactorial.dpow_null

theorem dpow_zero {x : A} (hx : x ∈ I) : dpow I 0 x = 1 :=
  by
  simp only [dpow]
  rw [if_pos hx, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, Ring.inverse_one]
#align divided_powers.of_invertible_factorial.dpow_zero DividedPowers.OfInvertibleFactorial.dpow_zero

theorem dpow_one {x : A} (hx : x ∈ I) : dpow I 1 x = x := by
  rw [dpow_eq_of_mem 1 hx, pow_one, Nat.factorial_one, Nat.cast_one, Ring.inverse_one, one_mul]
#align divided_powers.of_invertible_factorial.dpow_one DividedPowers.OfInvertibleFactorial.dpow_one

theorem dpow_mem {m : ℕ} (hm : m ≠ 0) {x : A} (hx : x ∈ I) : dpow I m x ∈ I :=
  by
  rw [dpow_eq_of_mem m hx]
  exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))
#align divided_powers.of_invertible_factorial.dpow_mem DividedPowers.OfInvertibleFactorial.dpow_mem

theorem dpow_add_dif_pos {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) {m : ℕ} (hmn : m < n)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.range (m + 1)).sum fun k : ℕ => dpow I k x * dpow I (m - k) y := by
  rw [dpow_eq_of_mem m (Ideal.add_mem I hx hy)]
  simp only [dpow]
  rw [Ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_isUnit hn_fac hmn), Finset.mul_sum, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk 
  have h_ch :
    (m.choose k : A) =
      (m.factorial : A) * (Ring.inverse k.factorial : A) * (Ring.inverse (m - k).factorial : A) :=
    by
    have hadd : m = m - k + k := (tsub_add_cancel_iff_le.mpr hk).symm
    simp only [← mul_assoc]
    rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ 
        (factorial_isUnit hn_fac (lt_of_le_of_lt (Nat.sub_le m k) hmn)),
      Ring.eq_mul_inverse_iff_mul_eq _ _ _ 
        (factorial_isUnit hn_fac (lt_of_le_of_lt hk hmn))]
    nth_rw 1 [hadd]
    nth_rw 3 [hadd]
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.add_choose_mul_factorial_mul_factorial]
  rw [if_pos hx, if_pos hy, h_ch, ← mul_assoc, ← mul_assoc,
    mul_comm (Ring.inverse ↑(m - k).factorial) (y ^ (m - k)), mul_assoc _ (x ^ k), ←
    mul_assoc (x ^ k), mul_comm (x ^ k * y ^ (m - k)) (Ring.inverse ↑(m - k).factorial)]
  ring_nf
#align divided_powers.of_invertible_factorial.dpow_add_dif_pos DividedPowers.OfInvertibleFactorial.dpow_add_dif_pos

theorem dpow_add {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) (m : ℕ) {x : A}
    (hx : x ∈ I) {y : A} (hy : y ∈ I) :
    dpow I m (x + y) = (Finset.range (m + 1)).sum fun k : ℕ => dpow I k x * dpow I (m - k) y :=
  by
  by_cases hmn : m < n
  · exact dpow_add_dif_pos hn_fac hmn hx hy
  · have h_sub : I ^ m ≤ I ^ n := Ideal.pow_le_pow (not_lt.mp hmn)
    rw [dpow_eq_of_mem m (Ideal.add_mem I hx hy)]
    simp only [dpow]
    have hxy : (x + y) ^ m = 0 :=
      by
      rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
      apply Set.mem_of_subset_of_mem h_sub (Ideal.pow_mem_pow (Ideal.add_mem I hx hy) m)
    rw [hxy, MulZeroClass.mul_zero, eq_comm]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_pos hx, if_pos hy, mul_assoc, mul_comm (x ^ k), mul_assoc, ← mul_assoc]
    apply mul_eq_zero_of_right
    rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
    have hIm : y ^ (m - k) * x ^ k ∈ I ^ m :=
      by
      have hadd : m = m - k + k :=
        by
        rw [eq_comm, tsub_add_cancel_iff_le]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      nth_rw 2 [hadd]
      rw [pow_add]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hy _) (Ideal.pow_mem_pow hx _)
    apply Set.mem_of_subset_of_mem h_sub hIm
#align divided_powers.of_invertible_factorial.dpow_add DividedPowers.OfInvertibleFactorial.dpow_add

theorem dpow_smul (m : ℕ) {a x : A} (hx : x ∈ I) : dpow I m (a * x) = a ^ m * dpow I m x := by
  rw [dpow_eq_of_mem m (Ideal.mul_mem_left I _ hx), dpow_eq_of_mem m hx, 
    mul_pow, ← mul_assoc, mul_comm _ (a ^ m), mul_assoc]
#align divided_powers.of_invertible_factorial.dpow_smul DividedPowers.OfInvertibleFactorial.dpow_smul

theorem dpow_mul_dif_pos {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) {m k : ℕ}
    (hkm : m + k < n) {x : A} (hx : x ∈ I) :
    dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x :=
  by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  have h_fac :
    Ring.inverse (m.factorial : A) * (Ring.inverse k.factorial : A) =
      ↑((m + k).choose m) * (Ring.inverse (m + k).factorial : A) :=
    by
    rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ (factorial_isUnit hn_fac hkm), 
      mul_assoc,
      Ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_isUnit hn_fac hm),
      Ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_isUnit hn_fac hk)]
    norm_cast; apply congr_arg
    rw [← Nat.add_choose_mul_factorial_mul_factorial, mul_comm, mul_comm _ m.factorial,
      Nat.choose_symm_add]
  rw [dpow_eq_of_mem _ hx, dpow_eq_of_mem _ hx, dpow_eq_of_mem _ hx, 
    mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m), 
    ← pow_add, ← mul_assoc, ← mul_assoc, h_fac]
#align divided_powers.of_invertible_factorial.dpow_mul_dif_pos DividedPowers.OfInvertibleFactorial.dpow_mul_dif_pos

theorem dpow_mul {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) (m k : ℕ)
    {x : A} (hx : x ∈ I) : dpow I m x * dpow I k x = ↑((m + k).choose m) * dpow I (m + k) x :=
  by
  by_cases hkm : m + k < n
  · exact dpow_mul_dif_pos hn_fac hkm hx
  · have hxmk : x ^ (m + k) = 0 := Ideal.mem_pow_eq_zero n (m + k) hnI (not_lt.mp hkm) hx
    rw [dpow_eq_of_mem m hx, dpow_eq_of_mem k hx, dpow_eq_of_mem (m + k) hx, 
      mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m), ← pow_add, hxmk,
      MulZeroClass.mul_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
#align divided_powers.of_invertible_factorial.dpow_mul DividedPowers.OfInvertibleFactorial.dpow_mul

theorem dpow_comp_dif_pos {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) {m k : ℕ} (hk : k ≠ 0)
    (hkm : m * k < n) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(mchoose m k) * dpow I (m * k) x :=
  by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem (m * k) hx, dpow_eq_of_mem _ (dpow_mem hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, MulZeroClass.zero_mul, pow_zero, mul_one, mchoose_zero, Nat.cast_one, one_mul]
  · have hkn : k < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left (Nat.pos_of_ne_zero hm0)) hkm
    rw [dpow_eq_of_mem _ hx]
    have h_fac :
      Ring.inverse (m.factorial : A) * (Ring.inverse k.factorial : A) ^ m =
        ↑(mchoose m k) * (Ring.inverse (m * k).factorial : A) :=
      by
      rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ (factorial_isUnit hn_fac hkm), 
        mul_assoc,
        Ring.inverse_mul_eq_iff_eq_mul _ _ _ (factorial_isUnit hn_fac hmn)]
      rw [Ring.inverse_pow_mul_eq_iff_eq_mul _ _ (factorial_isUnit hn_fac hkn)]
      rw [← mchoose_lemma _ hk]
      simp only [Nat.cast_mul, Nat.cast_pow]
      rw [mul_comm (m.factorial : A), mul_assoc]
    rw [mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc, h_fac]
#align divided_powers.of_invertible_factorial.dpow_comp_dif_pos DividedPowers.OfInvertibleFactorial.dpow_comp_dif_pos

theorem dpow_comp {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) (m : ℕ)
    {k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
    dpow I m (dpow I k x) = ↑(mchoose m k) * dpow I (m * k) x :=
  by
  by_cases hmk : m * k < n
  · exact dpow_comp_dif_pos hn_fac hk hmk hx
  · have hxmk : x ^ (m * k) = 0 := Ideal.mem_pow_eq_zero n (m * k) hnI (not_lt.mp hmk) hx
    rw [dpow_eq_of_mem _ (dpow_mem hk hx), dpow_eq_of_mem _ hx, dpow_eq_of_mem _ hx, 
      mul_pow, ← pow_mul, ← mul_assoc, mul_comm k, hxmk, 
      MulZeroClass.mul_zero, MulZeroClass.mul_zero, MulZeroClass.mul_zero]
#align divided_powers.of_invertible_factorial.dpow_comp DividedPowers.OfInvertibleFactorial.dpow_comp

/-- Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def dividedPowers {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A))
    (hnI : I ^ n = 0) : DividedPowers I
    where
  dpow := dpow I
  dpow_null {_ _} hx := dpow_null hx
  dpow_zero {_} hx := dpow_zero hx
  dpow_one {_} hx := dpow_one hx
  dpow_mem {_ _} hn hx := dpow_mem hn hx
  dpow_add m {_ _} hx hy := dpow_add hn_fac hnI m hx hy
  dpow_smul m _ _ hx := dpow_smul m hx
  dpow_mul m k {_} hx := dpow_mul hn_fac hnI m k hx
  dpow_comp m {_ _} hk hx := dpow_comp hn_fac hnI m hk hx
#align divided_powers.of_invertible_factorial.divided_powers DividedPowers.OfInvertibleFactorial.dividedPowers

lemma dpow_def {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0) (m : ℕ) (x : A) :
  (dividedPowers (hn_fac) (hnI)).dpow m x = 
    if (x ∈ I) then Ring.inverse (m.factorial : A) * x ^ m else 0 := rfl

end OfInvertibleFactorial

namespace OfSquareZero

variable {A : Type _} [CommRing A] {I : Ideal A} (hI2 : I ^ 2 = 0)

noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (by simp) hI2
#align divided_powers.of_square_zero.divided_powers DividedPowers.OfSquareZero.dividedPowers

-- TODO: generalize to I^p = 0 in a ring A with prime characteristic p
theorem dpow_of_two_le {n : ℕ} (hn : 2 ≤ n) (a : A) : (dividedPowers hI2) n a = 0 := by
  simp [dividedPowers, OfInvertibleFactorial.dpow_def]
  split_ifs with ha
  -- ; convert MulZeroClass.mul_zero _
  suffices : a ^ n = 0
  . rw [this, mul_zero]
  . exact Ideal.mem_pow_eq_zero 2 n hI2 hn ha
  rfl
#align divided_powers.of_square_zero.dpow_of_two_le DividedPowers.OfSquareZero.dpow_of_two_le

end OfSquareZero

-- Instead of 1.2.1, I formalize example 2 from [BO], Section 3.
namespace RatAlgebra

variable {R : Type _} [CommRing R] (I : Ideal R)

noncomputable def dpow : ℕ → R → R := fun n => OfInvertibleFactorial.dpow I n
#align divided_powers.rat_algebra.dpow DividedPowers.RatAlgebra.dpow

variable {I}

-- We may not need this, but I'll leave it here for now
theorem dpow_eq_of_mem (n : ℕ) {x : R} (hx : x ∈ I) : 
  dpow I n x = (Ring.inverse n.factorial : R) * x ^ n := by
  rw [dpow, OfInvertibleFactorial.dpow_eq_of_mem _ hx]
#align divided_powers.rat_algebra.dpow_def DividedPowers.RatAlgebra.dpow_eq_of_mem

variable [Algebra ℚ R]

variable (I)

noncomputable def dividedPowers : DividedPowers I
    where
  dpow := dpow I
  dpow_null {_ _} hx := OfInvertibleFactorial.dpow_null hx
  dpow_zero {_} hx := OfInvertibleFactorial.dpow_zero hx
  dpow_one {_} hx := OfInvertibleFactorial.dpow_one hx
  dpow_mem {_ _} hn hx := OfInvertibleFactorial.dpow_mem hn hx
  dpow_add n {_ _} hx hy :=
    OfInvertibleFactorial.dpow_add_dif_pos (Factorial.isUnit (n + 1 - 1)) n.lt_succ_self hx hy
  dpow_smul n {_ _} hx := OfInvertibleFactorial.dpow_smul n hx
  dpow_mul m k {_} hx :=
    OfInvertibleFactorial.dpow_mul_dif_pos (Factorial.isUnit (m + k + 1 - 1)) (m + k).lt_succ_self
      hx
  dpow_comp m k {_} hk hx :=
    OfInvertibleFactorial.dpow_comp_dif_pos (Factorial.isUnit (m * k + 1 - 1)) hk (lt_add_one _) hx
#align divided_powers.rat_algebra.divided_powers DividedPowers.RatAlgebra.dividedPowers

@[simp]
theorem dividedPowers_dpow_apply (n : ℕ) (x : R) : (dividedPowers I).dpow n x = dpow I n x :=
  rfl
#align divided_powers.rat_algebra.divided_powers_dpow_apply DividedPowers.RatAlgebra.dividedPowers_dpow_apply

lemma isUnitFactorial (n : ℕ) : IsUnit (n.factorial : ℚ) := by
  rw [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
  apply Nat.factorial_ne_zero

theorem dpow_eq_inv_fact_smul (n : ℕ) {x : R} (hx : x ∈ I) :
  dpow I n x = Ring.inverse (Nat.factorial n : ℚ) • x ^ n := by
  rw [dpow, OfInvertibleFactorial.dpow, if_pos hx]
  simp only [Algebra.smul_def, ← map_natCast (algebraMap ℚ R)]
  rw [Ring.inverse_mul_eq_iff_eq_mul, ← mul_assoc]
  apply symm
  convert @one_mul R _ _
  simp only [← map_mul, ← map_one (algebraMap ℚ R)]
  apply congr_arg
  apply symm
  rw [Ring.eq_mul_inverse_iff_mul_eq, one_mul]
  . apply isUnitFactorial
  . apply RingHom.isUnit_map
    apply isUnitFactorial

variable {I}

-- There are no other divided power structures on a ℚ-algebra.
theorem dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I :=
  by
  apply eq_of_eq_on_ideal
  intro n x hx
  have hn : IsUnit (n.factorial : R) := Factorial.isUnit n
  rw [dividedPowers_dpow_apply, dpow_eq_of_mem n hx, eq_comm, Ring.inverse_mul_eq_iff_eq_mul _ _ _ hn,
    factorial_mul_dpow_eq_pow _ _ _ hx]
#align divided_powers.rat_algebra.divided_powers_unique DividedPowers.RatAlgebra.dividedPowers_unique

end RatAlgebra

end DividedPowers

