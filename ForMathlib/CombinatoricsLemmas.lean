import Mathlib.Data.Nat.Choose.Vandermonde

--import multinomial 
--import multinomial
section Combinatorics

-- Because mathlib hasn't it yet!
@[eliminator]
theorem Nat.rec' {motive : Nat → Sort u}
    (zero : motive 0) (add_one : (n : Nat) → motive n → motive (n + 1)) (t : Nat) :
    motive t :=
  Nat.rec zero add_one t

/-- Number of possibilities of choosing m groups of n-element subsets out of mn elements -/
def mchoose (m n : ℕ) : ℕ :=
  Finset.prod (Finset.range m) fun p => Nat.choose (p * n + n - 1) (n - 1)
#align mchoose mchoose

theorem mchoose_zero (n : ℕ) : mchoose 0 n = 1 := by
  rw [mchoose, Finset.range_zero, Finset.prod_empty]
#align mchoose_zero mchoose_zero

theorem mchoose_zero' (m : ℕ) : mchoose m 0 = 1 := by
  simp only [mchoose, MulZeroClass.mul_zero, Nat.choose_self, Finset.prod_const_one]
#align mchoose_zero' mchoose_zero'

theorem mchoose_succ (m n : ℕ) :
    mchoose (m + 1) n = Nat.choose (m * n + n - 1) (n - 1) * mchoose m n := by
  simp only [mchoose, Finset.prod_range_succ, mul_comm]
#align mchoose_succ mchoose_succ

theorem mchoose_lemma (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    m.factorial * n.factorial ^ m * mchoose m n = (m * n).factorial :=
  by
  rw [← zero_lt_iff] at hn 
  induction' m  with m ih
  · rw [mchoose_zero, mul_one, MulZeroClass.zero_mul, Nat.factorial_zero, pow_zero, mul_one]
  · have hmn : (m + 1) * (m * n + n - 1).choose (n - 1) = (m * n + n).choose n :=
      by
      rw [←
        mul_left_inj' (Nat.mul_ne_zero (Nat.factorial_ne_zero (m * n)) (Nat.factorial_ne_zero n)), ←
        mul_assoc, ← mul_assoc, Nat.add_choose_mul_factorial_mul_factorial, ←
        Nat.mul_factorial_pred hn, mul_comm n _, ← mul_assoc, Nat.add_sub_assoc hn (m * n),
        mul_comm, mul_assoc ((m + 1) * (m * n + (n - 1)).choose (n - 1)), mul_assoc (m + 1), ←
        mul_assoc ((m * n + (n - 1)).choose (n - 1)), Nat.add_choose_mul_factorial_mul_factorial, ←
        Nat.mul_factorial_pred (Nat.add_pos_right _ hn), ← Nat.add_sub_assoc hn (m * n)]
      ring
    rw [mchoose_succ, Nat.factorial_succ, pow_succ, ← mul_assoc]
    conv_rhs => rw [Nat.succ_mul]
    rw [← Nat.add_choose_mul_factorial_mul_factorial, ← ih, ← hmn]
    ring_nf
#align mchoose_lemma mchoose_lemma

end Combinatorics

