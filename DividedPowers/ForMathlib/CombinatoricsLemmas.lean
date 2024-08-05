import Mathlib.Data.Nat.Choose.Vandermonde

--import multinomial
--import multinomial
section Combinatorics

-- Because mathlib hasn't it yet!
@[induction_eliminator]
def Nat.rec' {motive : Nat → Sort*}
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

theorem mchoose_one (n : ℕ) : mchoose 1 n = 1 := by
  simp only [mchoose, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, Nat.choose_self]

theorem mchoose_one' (m : ℕ) : mchoose m 1 = 1 := by
  simp only [mchoose, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, Nat.choose_zero_right, Finset.prod_const_one]

theorem mchoose_lemma (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    m.factorial * n.factorial ^ m * mchoose m n = (m * n).factorial :=
  by
  rw [← zero_lt_iff] at hn
  induction' m  with m ih
  · rw [mchoose_zero, mul_one, MulZeroClass.zero_mul, Nat.factorial_zero, pow_zero, mul_one]
  · --TODO: extract lemma hmn --
    -- (m.succ * n.succ).choose n.succ = m.succ * (m * n.succ + n).choose n (for any m, n)
    -- (m * n).choose n = m * (m.pred * n + n.pred).choose n.pred (for m ≥ 0, n > 0)
    have hmn : (m + 1) * (m * n + n - 1).choose (n - 1) = (m * n + n).choose n := by
      rw [←
        mul_left_inj' (Nat.mul_ne_zero (Nat.factorial_ne_zero (m * n)) (Nat.factorial_ne_zero n))]
      rw [← mul_assoc, ← mul_assoc, Nat.add_choose_mul_factorial_mul_factorial,
        ← Nat.mul_factorial_pred hn, mul_comm n _, ← mul_assoc, Nat.add_sub_assoc hn (m * n),
        mul_comm, mul_assoc ((m + 1) * (m * n + (n - 1)).choose (n - 1)), mul_assoc (m + 1), ←
        mul_assoc ((m * n + (n - 1)).choose (n - 1)), Nat.add_choose_mul_factorial_mul_factorial, ←
        Nat.mul_factorial_pred (Nat.add_pos_right _ hn), ← Nat.add_sub_assoc hn (m * n)]
      ring

    have hmn' : (m + 1) * (m * n + n - 1).choose (n - 1) = (m * n + n).choose n := by
      rw [←
        mul_left_inj' (Nat.mul_ne_zero (Nat.factorial_ne_zero (m * n)) (Nat.factorial_ne_zero n))]
      calc (m + 1) * (m * n + n - 1).choose (n - 1) * ((m * n).factorial * n.factorial) =
        (m + 1) * (m * n + n - 1).choose (n - 1) *
          ((m * n).factorial * (n * (n - 1).factorial)) := by rw [← Nat.mul_factorial_pred hn]
        _ = (m + 1) * n * ((m * n + n - 1).choose (n - 1) * (m * n).factorial * (n - 1).factorial) := by
          ring
        _ = (m + 1) * n * ((m * n + (n - 1)).choose (n - 1) * (m * n).factorial * (n - 1).factorial) := by
          rw [Nat.add_sub_assoc hn (m * n)]
        _ = (m + 1) * n * ((m * n + (n - 1)).factorial) := by
          rw [Nat.add_choose_mul_factorial_mul_factorial]
        _ = (m * n + n) * ((m * n + (n - 1)).factorial) := by
          ring
        _ = (m * n + n) * ((m * n + n - 1).factorial) := by
          rw [Nat.add_sub_assoc hn (m * n)]
        _ = (m * n + n).factorial := by rw [Nat.mul_factorial_pred (Nat.add_pos_right _ hn)]
        _ = (m * n + n).choose n * ((m * n).factorial * n.factorial) := by
            rw [← Nat.add_choose_mul_factorial_mul_factorial (m * n)]
            ring

    have hmn'' : (m + 1) * (m * n + n - 1).choose (n - 1) = (m * n + n).choose n := by
      set p := n - 1
      have : n = p + 1 := sorry
      rw [this, Nat.add_succ_sub_one, ← mul_left_inj'
        (Nat.mul_ne_zero (Nat.factorial_ne_zero (m * (p + 1))) (Nat.factorial_ne_zero (p + 1)))]
      calc (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1)).factorial * (p + 1).factorial)
        _ = (m + 1) * (p + 1) * ((m * (p + 1) + p).choose p * (m * (p + 1)).factorial * p.factorial) := by
          rw [Nat.factorial_succ p]
          ring
        _ = _ := by rw [Nat.add_choose_mul_factorial_mul_factorial]
        _ = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p + 1)).factorial * (p + 1).factorial := by
          rw [Nat.add_choose_mul_factorial_mul_factorial]
          rw [← add_assoc, Nat.factorial_succ]
          ring
        _ = (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p + 1)).factorial * (p + 1).factorial) := by
          ring

    /- have hnm'' : (m.succ * n.succ).choose n.succ = m.succ * (m * n.succ + n).choose n := by
      rw [←  mul_left_inj' (Nat.mul_ne_zero (Nat.factorial_ne_zero (m.succ * n.succ))
          (Nat.factorial_ne_zero n.succ))]
      calc (m.succ * n.succ).choose n.succ * ((m.succ * n.succ).factorial * n.succ.factorial) =
        ((m + 1) * (n + 1)).choose (n + 1) * (((m + 1) * (n + 1)).factorial * (n + 1).factorial) := rfl
        /- _ = ((m + 1) * (n + 1)).choose (n + 1) * (((m + 1) * (n + 1)).factorial * ((n + 1) * n.factorial)) := by
            rw [Nat.factorial_succ] -/
        _ = (((m * n + m  + (n + 1))).choose (n + 1) * ((m * n + m + n + 1)).factorial * (n + 1).factorial) := by
          ring_nf
        _ = _ := by rw [Nat.add_choose_mul_factorial_mul_factorial]
        _ = m.succ * (m * n.succ + n).choose n * ((m.succ * n.succ).factorial * n.succ.factorial) := by
          sorry -/
     /-  calc (m.succ * n.succ).choose n.succ =
        (m + 1) * (m * n + n - 1).choose (n - 1) *
          ((m * n).factorial * (n * (n - 1).factorial)) := by rw [← Nat.mul_factorial_pred hn]
        _ = (m + 1) * n * ((m * n + n - 1).choose (n - 1) * (m * n).factorial * (n - 1).factorial) := by
          ring
        _ = (m + 1) * n * ((m * n + (n - 1)).choose (n - 1) * (m * n).factorial * (n - 1).factorial) := by
          rw [Nat.add_sub_assoc hn (m * n)]
        _ = (m + 1) * n * ((m * n + (n - 1)).factorial) := by
          rw [Nat.add_choose_mul_factorial_mul_factorial]
        _ = (m * n + n) * ((m * n + (n - 1)).factorial) := by
          ring
        _ = (m * n + n) * ((m * n + n - 1).factorial) := by
          rw [Nat.add_sub_assoc hn (m * n)]
        _ = (m * n + n).factorial := by rw [Nat.mul_factorial_pred (Nat.add_pos_right _ hn)]
        _ = (m * n + n).choose n * ((m * n).factorial * n.factorial) := by
            rw [← Nat.add_choose_mul_factorial_mul_factorial (m * n)]
            ring -/

    rw [mchoose_succ, Nat.factorial_succ, pow_succ, ← mul_assoc]
    conv_rhs => rw [Nat.succ_mul]
    rw [← Nat.add_choose_mul_factorial_mul_factorial, ← ih, ← hmn]
    ring_nf

end Combinatorics
