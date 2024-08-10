import Mathlib.Data.Nat.Choose.Vandermonde

namespace Nat

/-- Number of possibilities of choosing `m` groups of `n`-element subsets out of `m * n` elements -/
def mchoose (m n : ℕ) : ℕ :=
  Finset.prod (Finset.range m) fun p => choose (p * n + n - 1) (n - 1)

theorem mchoose_zero (n : ℕ) : mchoose 0 n = 1 := by
  rw [mchoose, Finset.range_zero, Finset.prod_empty]

theorem mchoose_zero' (m : ℕ) : mchoose m 0 = 1 := by
  simp only [mchoose, MulZeroClass.mul_zero, choose_self, Finset.prod_const_one]

theorem mchoose_succ (m n : ℕ) :
    mchoose (m + 1) n = choose (m * n + n - 1) (n - 1) * mchoose m n := by
  simp only [mchoose, Finset.prod_range_succ, mul_comm]

theorem mchoose_one (n : ℕ) : mchoose 1 n = 1 := by
  simp only [mchoose, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

theorem mchoose_one' (m : ℕ) : mchoose m 1 = 1 := by
  simp only [mchoose, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

theorem choose_mul_add (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n + n).choose n = (m + 1) * (m * n + n - 1).choose (n - 1) := by 
  rw [← mul_left_inj' (mul_ne_zero (factorial_ne_zero (m * n)) (factorial_ne_zero n))]
  set p := n - 1 
  have hp : n = p + 1 := (succ_pred_eq_of_ne_zero hn).symm
  simp only [hp, add_succ_sub_one]
  calc 
    (m * (p + 1) + (p + 1)).choose (p + 1) * ((m * (p+1))! * (p+1)!) 
      = (m * (p + 1) + (p + 1)).choose (p + 1) * (m * (p+1))! * (p+1)! := by ring
    _ = (m * (p+ 1) + (p + 1))! := by rw [add_choose_mul_factorial_mul_factorial]
    _ = ((m * (p+ 1) + p) + 1)! := by ring_nf
    _ = ((m * (p + 1) + p) + 1) * (m * (p + 1) + p)! := by rw [factorial_succ]
    _ = (m * (p + 1) + p)! * ((p + 1) * (m + 1)) := by ring
    _ = ((m * (p + 1) + p).choose p * (m * (p+1))! * (p)!) * ((p + 1) * (m + 1)) := by rw [add_choose_mul_factorial_mul_factorial]
    _ = (m * (p + 1) + p).choose p * (m * (p+1))! * (((p + 1) * (p)!) * (m + 1)) := by ring
    _ = (m * (p + 1) + p).choose p * (m * (p+1))! * ((p + 1)! * (m + 1)) := by rw [factorial_succ]
    _ = (m + 1) * (m * (p + 1) + p).choose p * ((m * (p + 1))! * (p + 1)!) := by ring
  
theorem choose_mul_right (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by 
  by_cases hm : m = 0 
  · simp only [hm, zero_mul, choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [add_mul, one_mul, choose_mul_add _ hn]

theorem mchoose_lemma (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    m.factorial * n.factorial ^ m * mchoose m n = (m * n).factorial := by
  rw [← zero_lt_iff] at hn
  induction m with -- m ih
  | zero => rw [mchoose_zero, mul_one, MulZeroClass.zero_mul, factorial_zero, pow_zero, mul_one]
  | succ m ih => 
    calc (m+1)! * (n)! ^ (m+1) * mchoose (m + 1) n 
        = (m + 1)! *(n)! ^(m + 1) * ((m * n + n - 1).choose (n-1) * mchoose m n) := by rw [mchoose_succ]
      _ = ((m + 1) * (m * n + n - 1).choose (n-1)) * (m)! * (n)!  ^(m +1) * (mchoose m n) := by
        rw [factorial_succ]; ring 
      _ = ((m*n+n).choose n) * (m)! * (n)! ^ (m+1) * (mchoose m n) := by 
        rw [← choose_mul_add _ (not_eq_zero_of_lt hn)]
      _ = ((m*n+n).choose n) * (n)! * ((m)! * (n)! ^ m * (mchoose m n)) := by 
        rw [pow_succ]; ring_nf
      _ = (m  * n + n).choose n * (m * n)! * (n)! := by rw [ih]; ring
      _ = (m * n + n)! := by rw [add_choose_mul_factorial_mul_factorial]
      _ = ((m + 1)* n)! := by ring_nf


theorem mchoose_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) : 
    mchoose m n = (m * n).factorial / (m.factorial * n.factorial ^ m) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos m.factorial_pos (Nat.pow_pos (Nat.factorial_pos n))
  · rw [← mul_assoc, ← mchoose_lemma _ hn, mul_comm, ← mul_assoc]

open Multiset Finset

/- Can one define restricted Bell numbers ? 

For `m : Multiset ℕ`, `rBell m` counts the number of unordered partitions
of a set with `m.sum` elements. 
It is equal to `(m.sum)! / ((m.map fun i ↦ i !).prod * Π n ∈ m.toFinset.erase 0, (m.count n)!)
-/

/-- The number of partitions of a set of cardinality `m.sum` with parts of cardinalities given by `m` -/
def rBell (m : Multiset ℕ) : ℕ :=
  (m.sum)! / ((m.map fun n ↦ n !).prod * (∏ n in m.toFinset.erase 0, (m.count n)!)) 

theorem rBell_dvd (m : Multiset ℕ) :
    ((m.map fun n ↦ n !).prod * (∏ n in m.toFinset.erase 0, (m.count n)!)) ∣ (m.sum)! := by 
  suffices ∀ s : Finset ℕ, ∀ m : Multiset ℕ, m.toFinset = s → 
    ((m.map fun n ↦ n !).prod * (∏ n in m.toFinset.erase 0, (m.count n)!)) ∣ (m.sum)! by 
    exact this m.toFinset m rfl 
  intro s
  induction s using Finset.induction_on with 
  | empty => 
    intro m hs 
    rw [toFinset_eq_empty] at hs 
    simp [hs, prod_empty, mul_one]
  | @insert a s has hrec => 
    intro m hs
    let m' := m - replicate (m.count a) a 
    have hm' : count a m' = 0 := by simp [m']
    have hm : m = m' + replicate (m.count a) a := by 
      simp only [m']
      ext b 
      simp only [count_add, count_replicate, count_sub, m']
      split_ifs with hb 
      · simp [hb]
      · simp [hb]
    have hs' :m'.toFinset = s := by
      ext x
      simp only [m', mem_toFinset, ← one_le_count_iff_mem, count_sub]
      rw [Nat.one_le_iff_ne_zero, ne_eq, not_iff_comm, count_replicate]
      split_ifs with hx
      · simp  [← hx, has]
      · simp only [tsub_zero, count_eq_zero, not_iff_not]
        rw [← mem_toFinset, hs, mem_insert, iff_or_self, eq_comm]
        intro _; contradiction
    nth_rewrite 1 [hm]
    simp only [Multiset.map_add, map_replicate, Multiset.prod_add, prod_replicate]
    obtain ⟨k, hk⟩ := hrec m' hs'
    simp only [hs'] at hk
    by_cases ha0 : a = 0
    · simp [ha0]
      have : m.toFinset.erase 0 = s.erase 0 := by 
        ext x
        simp only [hs, ha0, erase_insert_eq_erase, mem_erase, ne_eq] 
      rw [this]
      conv_rhs => 
        rw [hm, Multiset.sum_add, Multiset.sum_replicate, ha0, smul_eq_mul, mul_zero, add_zero]
      rw [hk]
      rw [Finset.prod_congr rfl 
        (show ∀ x ∈ s.erase 0, (count x m)! = (count x m')! by 
          intro x hx
          apply congr_arg
          rw [hm, count_add, count_replicate, if_neg, add_zero]
          intro hx' 
          rw [← hx'] at hx
          exact has (Finset.mem_of_mem_erase hx))]
      apply Nat.dvd_mul_right
    · have this : (insert a s).erase 0 = insert a (s.erase 0) := by 
        ext x
        simp only [mem_erase, ne_eq, mem_insert]
        constructor
        · rintro ⟨hx, hx'⟩
          rcases hx' with (hx' | hx')
          · left; exact hx'
          · right; exact ⟨hx, hx'⟩
        · intro hx
          rcases hx with (hx | hx)
          · constructor
            rw [hx]; exact ha0
            left; exact hx
          · exact ⟨hx.1, Or.inr hx.2⟩
      have this' : a ∉ s.erase 0 := fun ha' ↦ has (Finset.mem_of_mem_erase ha')
      rw [hs, this, Finset.prod_insert this']
      rw [hm]
      simp only [count_add, count_replicate_self, sum_add, sum_replicate, smul_eq_mul, hm', zero_add]
      rw [Finset.prod_congr rfl
        (show ∀ x ∈ s.erase 0, (count x m' + count x (replicate (count a m) a))! = (count x m')! by 
          intro x hx 
          apply congr_arg
          rw [count_replicate, if_neg, add_zero]
          intro hx'; rw [hx'] at this'; exact this' hx)]
      rw [← add_choose_mul_factorial_mul_factorial m'.sum, hk]
      simp only [mul_assoc]
      conv_rhs => 
        rw [mul_comm]
        simp only [mul_assoc]
      apply mul_dvd_mul dvd_rfl
      conv_rhs =>
        rw [mul_comm]
      simp only [← mul_assoc]
      apply mul_dvd_mul _ dvd_rfl
      rw [← mchoose_lemma _ ha0]
      rw [mul_comm, mul_comm k]
      simp only [mul_assoc]
      apply mul_dvd_mul dvd_rfl
      apply Nat.dvd_mul_right
      
theorem rBell_mul_eq_factorial_sum (m : Multiset ℕ) : 
    rBell m * (m.map fun n ↦ n !).prod * (∏ n in m.toFinset.erase 0, (m.count n)!) = (m.sum)! := by 
  rw [mul_assoc]
  exact Nat.div_mul_cancel (rBell_dvd m)

@[simp] lemma _root_.Multiset.replicate_toFinset {α : Type*} [DecidableEq α] (n : ℕ) (a : α) : 
    (replicate n a).toFinset = if n = 0 then ∅ else {a} := by 
  ext x
  simp only [mem_toFinset, Finset.mem_singleton, mem_replicate]
  split_ifs with hn <;> simp [hn]

theorem rBell_replicate (m n : ℕ) : rBell (replicate m n) = mchoose m n := by 
  by_cases hn : n = 0
  · rw [hn, mchoose_zero']
    unfold rBell
    simp only [sum_replicate, smul_eq_mul, mul_zero, factorial_zero]
    simp only [map_replicate, factorial_zero, prod_replicate, one_pow, one_mul]
    rw [Finset.prod_eq_one, Nat.div_one]
    intro x hx
    simp only [replicate_toFinset, mem_erase, ne_eq] at hx
    simp only [count_replicate, if_neg (Ne.symm hx.1), factorial_zero]
  · rw [mchoose_eq m hn]
    unfold rBell 
    apply congr_arg₂ 
    · rw [sum_replicate]
      simp only [smul_eq_mul]
    · simp only [map_replicate, prod_replicate]
      simp only [replicate_toFinset]
      split_ifs with hm
      · simp [hm]
      · suffices ({n} : Finset ℕ).erase 0 = {n} by
          simp only [this, Finset.prod_singleton, count_replicate_self, mul_comm]
        ext x
        simp only [mem_erase, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
        intro hx
        simp [hx, hn]


