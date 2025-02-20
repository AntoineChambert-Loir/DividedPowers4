import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Multinomial

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities given by `m`.
The definition presents it as an integer.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Multiset.bell_zero`: `Multiset.bell 0 = 1`

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
    `m.bell * (m.map (fun j ↦ j !)).prod *
      Finset.prod (m.toFinset.erase 0) (fun j ↦ (m.count j)!) = m.sum !`

* `Nat.uniformBell_mul_eq`  shows that
    `uniformBell m n * n.factorial ^ m * m.factorial = (m * n).factorial`

* `Nat.uniformBell_zero`, `Nat.uniformBell_zero'`, `Nat.uniformBell_one`, `Nat.uniformBell_one':
compute `Nat.uniformBell` when one of the parameters is `0` or `1`

* `Nat.uniformBell_succ` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

-/

-- In PR #15644

open Multiset Nat

theorem Nat.choose_mul_add (m) {n : ℕ} (hn : n ≠ 0) :
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

theorem Nat.choose_mul_right (m) {n : ℕ} (hn : n ≠ 0) :
    (m * n).choose n = m * (m * n - 1).choose (n - 1) := by
  by_cases hm : m = 0
  · simp only [hm, zero_mul, choose_eq_zero_iff]
    exact Nat.pos_of_ne_zero hn
  · set p := m - 1; have hp : m = p + 1 := (succ_pred_eq_of_ne_zero hm).symm
    simp only [hp]
    rw [add_mul, one_mul, choose_mul_add _ hn]


@[simp] lemma Multiset.replicate_toFinset {α : Type*} [DecidableEq α] (n : ℕ) (a : α) :
    (replicate n a).toFinset = if n = 0 then ∅ else {a} := by
  ext x
  simp only [mem_toFinset, Finset.mem_singleton, mem_replicate]
  split_ifs with hn <;> simp [hn]

def Multiset.bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    (m.toFinset.erase 0).prod
      (fun k ↦ Finset.prod (Finset.range (m.count k)) fun j ↦ (j * k + k - 1).choose (k-1))

@[simp]
theorem Multiset.bell_zero : bell 0 = 1 := by unfold bell; simp

@[to_additive]
theorem Multiset.map_prod_pow_count {ι α : Type*} [DecidableEq ι] (m : Multiset ι) [CommMonoid α]
    (f : ι → α) :
     m.toFinset.prod (fun a ↦ f a ^ count a m) = (m.map f).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons n m h =>
    simp only [toFinset_cons, prod_cons, map_cons]
    by_cases hn : n ∈ m
    · have hn' : n ∈ m.toFinset := by exact mem_toFinset.mpr hn
      rw [Finset.insert_eq_of_mem hn']
      rw [← Finset.prod_erase_mul _ _ hn'] at h ⊢
      rw [count_cons_self, pow_add, pow_one, ← mul_assoc, mul_comm]
      rw [← h]
      apply congr_arg₂ _ rfl
      apply congr_arg₂ _ _ rfl
      apply Finset.prod_congr rfl
      intro x hx
      apply congr_arg₂ _ rfl
      rw [count_cons, if_neg (Finset.ne_of_mem_erase hx), add_zero]
    · have hn' : n ∉ m.toFinset := by simp [hn]
      rw [Finset.prod_insert hn']
      apply congr_arg₂
      · simp only [count_cons_self, pow_add, pow_one, count_eq_zero.mpr hn, zero_smul, zero_add]
      · rw [← h]
        apply Finset.prod_congr rfl
        intro i hi
        rw [count_cons, pow_add, if_neg (ne_of_mem_of_not_mem hi hn'), pow_zero, mul_one]

 @[to_additive]
theorem Multiset.prod_pow_count {α : Type*} [DecidableEq α] (m : Multiset α) [CommMonoid α] :
     m.toFinset.prod (fun i ↦ i ^ count i m) = m.prod := by
  rw [← map_id m, ← m.map_prod_pow_count, map_id]
  simp only [id_eq]

theorem Nat.bell_mul_eq_lemma {x : ℕ} (hx : x ≠ 0) (c : ℕ) :
    x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)! := by
  induction c with
  | zero => simp
  | succ c hrec =>
    suffices  x ! ^ (c + 1) * (c + 1) ! = x ! * (c + 1) * (x ! ^ c * c !) by
      rw [this]
      rw [← mul_assoc]
      simp only [Finset.range_succ, Finset.mem_range, lt_self_iff_false, not_false_eq_true,
        Finset.prod_insert]
      simp only [mul_assoc]
      rw [mul_comm ((c * x + x - 1).choose (x-1))]
      rw [← mul_assoc]
      rw [mul_comm]
      simp only [← mul_assoc]
      rw [hrec]
      have : (x * c)! * ((c * x + x - 1).choose (x - 1)) * x ! * (c + 1)
        = ((c + 1) * ((c * x + x - 1).choose (x - 1))) * (x * c)! *  x ! := by
        ring_nf
      rw [this]
      rw [← Nat.choose_mul_add c hx]
      rw [mul_comm c x]
      rw [Nat.add_choose_mul_factorial_mul_factorial (x * c) x]
      rw [mul_add, mul_one]
    rw [factorial_succ, pow_succ]
    ring_nf

theorem Multiset.bell_mul_eq (m : Multiset ℕ) :
    m.bell * (m.map (fun j ↦ j !)).prod *
      Finset.prod (m.toFinset.erase 0) (fun j ↦ (m.count j)!) = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj]
  · simp only [← mul_assoc]
    rw [Nat.multinomial_spec]
    simp only [mul_assoc]
    rw [mul_comm]
    apply congr_arg₂
    · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib]
      rw [← Multiset.map_prod_pow_count]
      suffices this : _ by
        by_cases hm : 0 ∈ m.toFinset
        · rw [← Finset.prod_erase_mul _ _ hm]
          rw [← Finset.prod_erase_mul _ _ hm]
          simp only [factorial_zero, one_pow, mul_one, zero_mul]
          exact this
        · nth_rewrite 1 [← Finset.erase_eq_of_not_mem hm]
          nth_rewrite 3 [← Finset.erase_eq_of_not_mem hm]
          exact this
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro x hx
      rw [← mul_assoc, bell_mul_eq_lemma]
      simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
      simp only [ne_eq, hx.1, not_false_eq_true]
    · apply congr_arg
      rw [← Multiset.sum_nsmul_count]
      simp only [smul_eq_mul, mul_comm]
  · rw [← Nat.pos_iff_ne_zero]
    apply Finset.prod_pos
    exact fun _ _ ↦ Nat.factorial_pos _

theorem Multiset.bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map (fun j ↦ j !)).prod *
      Finset.prod (m.toFinset.erase 0) (fun j ↦ (m.count j)!)) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    apply Nat.mul_pos
    · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.multiset_prod_pos, mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun _ _ ↦ Nat.factorial_pos _
    · apply Finset.prod_pos
      exact fun _ _ ↦ Nat.factorial_pos _

def Nat.uniformBell (m n : ℕ) : ℕ := bell (replicate m n)

theorem Nat.uniformBell_eq (m n : ℕ) : m.uniformBell n =
    Finset.prod (Finset.range m) fun p => Nat.choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [replicate_toFinset]
  split_ifs with hm
  · simp  [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

theorem Nat.uniformBell_zero (n : ℕ) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]

theorem Nat.uniformBell_zero' (m : ℕ) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]

theorem Nat.uniformBell_succ (m n : ℕ) :
    uniformBell (m+1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

theorem uniformBell_one (n : ℕ) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

theorem uniformBell_one' (m : ℕ) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, ge_iff_le, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

theorem uniformBell_mul_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * n.factorial ^ m * m.factorial = (m * n).factorial := by
  convert bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [replicate_toFinset]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset ℕ).erase 0 = ∅ from rfl,  Finset.prod_empty]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp

theorem uniformBell_eq_div (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n = (m * n).factorial / (n.factorial ^ m * m.factorial) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos (Nat.factorial_pos n)) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]


namespace Nat

#exit

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
