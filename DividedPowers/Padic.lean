/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowers.RatAlgebra
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace PadicInt

open DividedPowers DividedPowers.OfInvertibleFactorial Nat Ring

variable (p : ℕ) [hp : Fact p.Prime]

theorem padicValNat_factorial_lt_of_ne_zero (p : ℕ) {n : ℕ} (hn : n ≠ 0) [hp : Fact (Nat.Prime p)] :
    padicValNat p n.factorial < n := by
  have hpn : ((p - 1 : ℕ) : ℝ) * (padicValNat p n ! : ℝ) = n - (p.digits n).sum := by
    rw [← cast_mul, sub_one_mul_padicValNat_factorial n, cast_sub (digit_sum_le p n)]
  have hp1 : 0 < p - 1 := zero_lt_sub_of_lt  (Nat.Prime.one_lt hp.elim)
  rw [mul_comm, ← eq_div_iff_mul_eq (_root_.ne_of_gt (Nat.cast_pos.mpr hp1))] at hpn
  rw [← Nat.cast_lt (α := ℝ), hpn, div_lt_iff₀ (Nat.cast_pos.mpr hp1)]
  have hnil : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  calc (n : ℝ) - ↑(p.digits n).sum
    _ < n := by
      apply sub_lt_self _
      exact_mod_cast Nat.sum_pos_iff_exists_pos.mpr ⟨(p.digits n).getLast hnil,
        List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩
    _ ≤ ↑n * ↑(p - 1) := by
      conv_lhs => rw [← mul_one (n : ℝ)]
      gcongr
      simp only [one_le_cast]
      exact hp1

theorem padicValNat_factorial_le (p n : ℕ) [Fact (Nat.Prime p)] :
    padicValNat p n.factorial ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

/-- The family `ℕ → ℚ_[p] → ℚ_[p]` given by `dpow n x = x ^ n / n!`. -/
private noncomputable def dpow' : ℕ → ℚ_[p] → ℚ_[p] := fun m x => inverse (m ! : ℚ_[p]) * x ^ m

lemma dpow'_norm_le_of_ne_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : ‖dpow' p n x‖ ≤ (p : ℝ)⁻¹ := by
  unfold dpow'
  by_cases hx0 : x = 0
  · rw [hx0]
    simp only [inverse_eq_inv', coe_zero, ne_eq, hn, not_false_eq_true, zero_pow, mul_zero,
      norm_zero, inv_nonneg, cast_nonneg]
  · have hlt : (padicValNat p n.factorial : ℤ) < n := by
      exact_mod_cast padicValNat_factorial_lt_of_ne_zero p hn
    have hnorm : 0 < ‖(n ! : ℚ_[p])‖ := by
      simp only [norm_pos_iff, ne_eq, cast_eq_zero]
      exact factorial_ne_zero n
    rw [← zpow_neg_one, ← Nat.cast_one (R := ℤ)]
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simp only [inverse_eq_inv', padicNormE.mul, norm_inv, _root_.norm_pow, padic_norm_e_of_padicInt,
      cast_one, Int.reduceNeg, neg_add_cancel, zpow_zero]
    rw [norm_eq_zpow_neg_valuation hx0, inv_mul_lt_one₀ hnorm, Padic.norm_eq_zpow_neg_valuation
      (cast_ne_zero.mpr n.factorial_ne_zero), ← zpow_natCast, ← zpow_mul]
    gcongr
    · exact_mod_cast Nat.Prime.one_lt hp.elim
    · simp only [neg_mul, Padic.valuation_natCast, neg_lt_neg_iff]
      apply lt_of_lt_of_le hlt
      conv_lhs => rw [← one_mul (n : ℤ)]
      gcongr
      norm_cast
      rwa [← PadicInt.mem_span_pow_iff_le_valuation x hx0, pow_one]

lemma dpow'_int (n : ℕ) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖dpow' p n x‖ ≤ 1 := by
  unfold dpow'
  by_cases hn : n = 0
  · simp only [hn, factorial_zero, cast_one, inverse_one, pow_zero, mul_one, norm_one, le_refl]
  · apply le_trans (dpow'_norm_le_of_ne_zero p hn hx)
    rw [← zpow_neg_one, ← zpow_zero ↑p]
    gcongr
    · exact_mod_cast Nat.Prime.one_le hp.elim
    · norm_num

/- lemma dpow'_int (n : ℕ) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖dpow' p n x‖ ≤ 1 := by
  unfold dpow'
  by_cases hx : x = 0
  · rw [hx]
    simp only [coe_zero, padicNormE.mul, _root_.norm_pow, norm_zero]
    by_cases hn : n = 0
    · rw [hn]
      simp only [factorial_zero, cast_one, inverse_one, norm_one, pow_zero, mul_one, le_refl]
    · rw [zero_pow hn, mul_zero]
      exact zero_le_one
  · have hle : (padicValNat p n.factorial : ℤ) ≤ n := by
      exact_mod_cast padicValNat_factorial_le p n
    rw [Padic.norm_le_one_iff_val_nonneg, inverse_eq_inv', Padic.valuation_mul
      (inv_ne_zero (cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
      (pow_ne_zero _ (coe_ne_zero.mpr hx)), Padic.valuation_pow, Padic.valuation_inv]
    simp only [Padic.valuation_natCast, valuation_coe, le_neg_add_iff_add_le, add_zero]
    apply le_trans hle
    conv_lhs => rw [← mul_one (n : ℤ)]
    gcongr
    norm_cast
    rwa [← PadicInt.mem_span_pow_iff_le_valuation x hx, pow_one] -/

lemma coe_mem_ideal_span {x y : ℤ_[p]} (h : x ∈ Ideal.span {y}) :
    (x : ℚ_[p]) ∈ Ideal.span {↑y} := by
  simp only [Ideal.mem_span_singleton, dvd_iff_exists_eq_mul_left] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  rw [hc, coe_mul]

variable {p}

/-- The coercion map `ℤ_[p] → ℚ_[p]` as a `RingHom`. -/
def coeRingHom : ℤ_[p] →+* ℚ_[p] where
  toFun        := fun x ↦ ↑x
  map_one'     := rfl
  map_mul' x y := by simp [coe_mul]
  map_zero'    := rfl
  map_add' x y := by simp [coe_add]

@[simp]
lemma coeRingHom_apply (x : ℤ_[p]) :
  coeRingHom x = ↑x := rfl

lemma coe_sum {α : Type*} (s : Finset α) (f : α → ℤ_[p]) :
    (((∑ z ∈ s, f z) : ℤ_[p]) : ℚ_[p]) = ∑ z ∈ s, (f z : ℚ_[p]) := by
  simp only [← coeRingHom_apply, map_sum coeRingHom f s]

variable (p) [DecidablePred fun x ↦ x ∈ Ideal.span {(p : ℤ_[p])}]

/-- The family `ℕ → Ideal.span {(p : ℤ_[p])} → ℤ_[p]` given by `dpow n x = x ^ n / n!`. -/
noncomputable def dpow : ℕ → ℤ_[p] → ℤ_[p] :=
  fun n x ↦ if hx : x ∈ Ideal.span {(p : ℤ_[p])} then ⟨dpow' p n x, dpow'_int p n hx⟩ else 0

private theorem dpow_mem {m : ℕ} {x : ℤ_[p]} (hm : m ≠ 0) (hx : x ∈ Ideal.span {↑p}) :
    dpow p m x ∈ Ideal.span {↑p} := by
  have hiff := PadicInt.norm_le_pow_iff_mem_span_pow (dpow p m x) 1
  rw [pow_one] at hiff
  rw [← hiff]
  simp only [dpow, dif_pos hx, cast_one, zpow_neg_one]
  exact dpow'_norm_le_of_ne_zero p hm hx

/-- The family `ℕ → Ideal.span {(p : ℤ_[p])} → ℤ_[p]` given by `dpow n x = x ^ n / n!` is a
  divided power structure on the `ℤ_[p]`-ideal `(p)`. -/
noncomputable def dividedPowers : DividedPowers (Ideal.span {(p : ℤ_[p])}) where
  dpow      := dpow p
  dpow_null hx := by rw [dpow, dif_neg hx]
  dpow_zero hx := by
    rw [dpow, dif_pos hx]
    simp only [dpow', factorial_zero, cast_one, inverse_one, pow_zero, mul_one]
    exact Subtype.ext PadicInt.coe_one
  dpow_one hx := by
    rw [dpow, dif_pos hx]
    simp [dpow', factorial_one, cast_one, inverse_one, pow_one, one_mul, Subtype.coe_eta]
  dpow_mul {n a x} hx :=  by
    have hax : a * x ∈ Ideal.span {↑p} := Ideal.mul_mem_left _ _ hx
    simp only [dpow, dif_pos hx, dif_pos hax, dpow']
    apply Subtype.ext
    simp only [inverse_eq_inv', coe_mul, coe_pow]
    ring
  dpow_mem hm hx  := dpow_mem p hm hx
  dpow_add {n x y} hx hy := by
    classical
    have hx' : (x : ℚ_[p]) ∈ Ideal.span {↑p} := by exact_mod_cast coe_mem_ideal_span p hx
    have hy' : (y : ℚ_[p]) ∈ Ideal.span {↑p} := by exact_mod_cast coe_mem_ideal_span p hy
    have hxy : x + y ∈ Ideal.span {↑p} := Ideal.add_mem _ hx hy
    have hxy' : (x + y : ℚ_[p]) ∈ Ideal.span {↑p} := by exact_mod_cast coe_mem_ideal_span p hxy
    simp only [dpow, dif_pos hx, dif_pos hy, dif_pos hxy]
    have heq := (RatAlgebra.dividedPowers (Ideal.span {(p : ℚ_[p])})).dpow_add (n := n) hx' hy'
    simp only [RatAlgebra.dividedPowers, RatAlgebra.dpow, OfInvertibleFactorial.dpow, if_pos hx',
      if_pos hy', if_pos hxy'] at heq
    apply Subtype.ext
    simp only [coe_add, coe_sum, coe_mul]
    exact  heq
  mul_dpow {m n x} hx := by
    classical
    simp only [dpow, dpow', dif_pos hx]
    have hx' : (x : ℚ_[p]) ∈ Ideal.span {↑p} := by exact_mod_cast coe_mem_ideal_span p hx
    have heq := (RatAlgebra.dividedPowers (Ideal.span {(p : ℚ_[p])})).mul_dpow (m := m) (n := n) hx'
    simp only [RatAlgebra.dividedPowers, RatAlgebra.dpow, OfInvertibleFactorial.dpow,
      if_pos hx'] at heq
    exact Subtype.ext heq
  dpow_comp {m n x} hn hx := by
    classical
    have hx' : (x : ℚ_[p]) ∈ Ideal.span {↑p} := by exact_mod_cast coe_mem_ideal_span p hx
    have hmem : dpow p n x ∈ Ideal.span {↑p} := dpow_mem p hn hx
    have hmem' : inverse (n ! : ℚ_[p]) * ↑x ^ n ∈ Ideal.span {↑p} := by
      have h : (dpow p n x : ℚ_[p]) ∈ Ideal.span {↑p} := by exact_mod_cast coe_mem_ideal_span p hmem
      simp only [dpow, dif_pos hx, dpow'] at h
      exact h
    rw [dpow, dif_pos hmem]
    simp only [dpow, dif_pos hx]
    apply Subtype.ext
    have heq := (RatAlgebra.dividedPowers (Ideal.span {(p : ℚ_[p])})).dpow_comp (m := m) hn hx'
    simp only [RatAlgebra.dividedPowers, RatAlgebra.dpow, OfInvertibleFactorial.dpow,
      if_pos hx', if_pos hmem'] at heq
    simp only [dpow', coe_mul]
    exact heq

end PadicInt
