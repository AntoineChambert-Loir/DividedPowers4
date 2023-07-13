/- for not_eq_or_aux
! This file was ported from Lean 3 source module basic_lemmas
-/
-- for not_eq_or_aux
import Mathbin.Data.Finset.Basic
import Mathbin.Algebra.Order.Sub.Basic
import Mathbin.Data.Finset.NatAntidiagonal
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.Data.Finset.Sym

-- for tsub_tsub_tsub_cancel_left
-- for tsub_tsub_tsub_cancel_left
-- for 4-fold sums
-- for 4-fold sums
-- for 4-fold sums (might not be optimal)
-- for 4-fold sums (might not be optimal)
/- -- Not used anymore
-- The "unused arguments" linter incorrectly flags this (?!)
-- To help distinguish the extreme cases in a finset.range(n+1).sum
lemma not_eq_or_aux {n m : ℕ} (hn : n ≠ 0) (hm : m ∈ finset.range(n + 1)) : m ≠ 0 ∨ n - m ≠ 0 :=
begin
  simp only [finset.mem_range, nat.lt_succ_iff] at hm,
  by_contradiction h,
  simp only [not_or_distrib, ne.def, not_not, tsub_eq_zero_iff_le, not_le, not_lt] at h,
  apply hn, rw ← le_zero_iff, rw ← h.1, exact h.2, 
end -/
/- -- Not used anymore
-- The "unused arguments" linter incorrectly flags this (?!)
-- To help distinguish the extreme cases in a finset.range(n+1).sum
lemma not_eq_or_aux {n m : ℕ} (hn : n ≠ 0) (hm : m ∈ finset.range(n + 1)) : m ≠ 0 ∨ n - m ≠ 0 :=
begin
  simp only [finset.mem_range, nat.lt_succ_iff] at hm,
  by_contradiction h,
  simp only [not_or_distrib, ne.def, not_not, tsub_eq_zero_iff_le, not_le, not_lt] at h,
  apply hn, rw ← le_zero_iff, rw ← h.1, exact h.2, 
end -/
/- -- Now in mathlib
lemma tsub_tsub_tsub_cancel_left {α : Type*} [add_comm_semigroup α] [partial_order α]
  [has_exists_add_of_le α] [covariant_class α α has_add.add has_le.le] [has_sub α] 
  [has_ordered_sub α] [contravariant_class α α has_add.add has_le.le] {a b c : α} (hcb : c ≤ b)
  (hab : b ≤ a) : a - c - (a - b) = b - c := 
by rw [tsub_eq_iff_eq_add_of_le (tsub_le_tsub_left hcb a), tsub_add_eq_add_tsub hcb, add_comm, 
  tsub_add_cancel_of_le hab] -/
/- -- Now in mathlib
lemma tsub_tsub_tsub_cancel_left {α : Type*} [add_comm_semigroup α] [partial_order α]
  [has_exists_add_of_le α] [covariant_class α α has_add.add has_le.le] [has_sub α] 
  [has_ordered_sub α] [contravariant_class α α has_add.add has_le.le] {a b c : α} (hcb : c ≤ b)
  (hab : b ≤ a) : a - c - (a - b) = b - c := 
by rw [tsub_eq_iff_eq_add_of_le (tsub_le_tsub_left hcb a), tsub_add_eq_add_tsub hcb, add_comm, 
  tsub_add_cancel_of_le hab] -/
/- -- Not used anymore
lemma nat.self_sub_sub_eq {u v n : ℕ} (huv : v ≤ u) (hun : u ≤ n) :
  n - v - (n - u) = u - v :=
tsub_tsub_tsub_cancel_left hun
/- begin
  rw nat.sub_eq_iff_eq_add (tsub_le_tsub_left h n),
  rw ← nat.sub_add_comm h,
  rw add_comm,
  rw nat.sub_add_cancel h', 
end -/ -/
/- -- Not used anymore
lemma nat.self_sub_sub_eq {u v n : ℕ} (huv : v ≤ u) (hun : u ≤ n) :
  n - v - (n - u) = u - v :=
tsub_tsub_tsub_cancel_left hun
/- begin
  rw nat.sub_eq_iff_eq_add (tsub_le_tsub_left h n),
  rw ← nat.sub_add_comm h,
  rw add_comm,
  rw nat.sub_add_cancel h', 
end -/ -/
section Classical

open scoped Classical

theorem Function.extend_apply_first {α β γ : Type _} (f : α → β) (g : α → γ) (e' : β → γ)
    (hf : ∀ a b : α, f a = f b → g a = g b) (a : α) : Function.extend f g e' (f a) = g a :=
  by
  simp only [Function.extend_def, dif_pos, exists_apply_eq_apply]
  apply hf
  exact Classical.choose_spec (exists_apply_eq_apply f a)
#align function.extend_apply_first Function.extend_apply_first

end Classical

section FourFoldSums

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- This lemma is awkward and mathematically obvious, 
just rewrite the sum using the variable x which determines y, z, t.
However, one of its points is to reduce a 4-fold sum to a 2-fold sum.  -/
/-- The sum of f(x, y) on x + y = m and z + t = n and x + z = u and y + t = v 
  is equal to the sum of  f(x, y) on x + y = m
  provided f (x, y) vanishes if x > u or y > v.
-/
theorem rewriting_4_fold_sums {α : Type _} [CommSemiring α] {m n u v : ℕ} (h : m + n = u + v)
    (f : ℕ × ℕ → α) {g : (ℕ × ℕ) × ℕ × ℕ → α} (hgf : g = fun x => f (x.fst.fst, x.fst.snd))
    (hf : ∀ x : ℕ × ℕ, u < x.fst ∨ v < x.snd → f x = 0) :
    (Finset.filter
            (fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
            (Finset.Nat.antidiagonal m ×ˢ Finset.Nat.antidiagonal n)).Sum
        g =
      (Finset.Nat.antidiagonal m).Sum f :=
  by
  let q := fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst
  have hq :
    ∀
      x ∈
        Finset.filter
          (fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
          (Finset.Nat.antidiagonal m ×ˢ Finset.Nat.antidiagonal n),
      x.fst ∈ Finset.Nat.antidiagonal m :=
    by intro x; simp; intro h'; simp [h']
  rw [← Finset.sum_fiberwise_of_maps_to hq]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij; simp only [Finset.Nat.mem_antidiagonal] at hij 
  rw [Finset.sum_filter]; rw [Finset.sum_filter]
  simp_rw [← ite_and]
  suffices hf' :
    ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j)) (g x) 0 =
        ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j)) 1 0 *
          f ⟨i, j⟩
  rw [Finset.sum_congr rfl fun x hx => hf' x]
  rw [← Finset.sum_mul]
  by_cases hij' : i ≤ u ∧ j ≤ v
  · conv_rhs => rw [← one_mul (f ⟨i, j⟩)]
    apply congr_arg₂ _ _ rfl
    rw [Finset.sum_eq_single (⟨⟨i, j⟩, ⟨u - i, v - j⟩⟩ : (ℕ × ℕ) × ℕ × ℕ)]
    simp only [Nat.add_sub_of_le hij'.1, Nat.add_sub_of_le hij'.2, eq_self_iff_true, and_self_iff,
      if_true]
    · rintro ⟨⟨x, y⟩, ⟨z, t⟩⟩ hb hb'; rw [if_neg]; intro hb''
      simp only [Finset.mem_product, Finset.Nat.mem_antidiagonal] at hb 
      simp only [Ne.def, Prod.mk.inj_iff, not_and, and_imp] at hb' 
      simp only [Prod.mk.inj_iff] at hb'' 
      specialize hb' hb''.2.1 hb''.2.2
      rw [hb''.2.1, hb''.2.2] at hb 
      apply hb'
      apply Nat.add_left_cancel; rw [Nat.add_sub_of_le hij'.1, ← hb''.2.1, hb''.1.1]
      apply Nat.add_left_cancel; rw [Nat.add_sub_of_le hij'.2, ← hb''.2.2, hb''.1.2]
    · intro hb; rw [if_neg]; intro hb'; apply hb
      simp only [eq_self_iff_true, and_true_iff] at hb' 
      simp only [Finset.mem_product, Finset.Nat.mem_antidiagonal]
      apply And.intro hij
      apply Nat.add_left_cancel; rw [h, ← hij]
      conv_rhs => rw [← hb'.1, ← hb'.2]
      simp only [← add_assoc, add_left_inj]
      simp only [add_assoc, add_right_inj]
      apply add_comm
  · simp only [not_and_or, not_le] at hij' 
    rw [hf ⟨i, j⟩ hij', MulZeroClass.mul_zero]
  · intro x
    split_ifs with hx
    · simp only [one_mul, hgf]; rw [hx.2]
    · rw [MulZeroClass.zero_mul]
#align rewriting_4_fold_sums rewriting_4_fold_sums

/- -- Unused
lemma rewriting_4_fold_sums' {m n u v : ℕ} 
  (h : m + n = u + v) (f : ℕ × ℕ → ℕ) {g : (ℕ × ℕ) × ℕ × ℕ → ℕ}
  (hgf : g = λ x, f(x.fst.fst, x.fst.snd) ) 
  (hf : ∀ (x : ℕ × ℕ), u < x.fst ∨ v < x.snd → f x = 0) :
  (finset.nat.antidiagonal m).sum
    (λ (y : ℕ × ℕ),
       (finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), (λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst) x = y)
          (finset.filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), x.fst.fst + x.snd.fst = 
            u ∧ x.fst.snd + x.snd.snd = v)
             (finset.nat.antidiagonal m ×ˢ finset.nat.antidiagonal n))).sum g) =
  (finset.nat.antidiagonal m).sum (λ (ij : ℕ × ℕ), f ⟨ij.fst, ij.snd⟩) := 
begin
rw ← rewriting_4_fold_sums, --  h f hgf hf
end
-/
/- TODO : There should be some general rewriting pattern 
for sums indexed by finset.nat_tuple_antidiagonal 
This one would first rewrite to 
(finset.nat_tuple_antidiagonal 4 n).sum (λ x, f(x0, x1, x2, x3)) 
and then one would apply the permutation (13)(24) -/
/-- Rewrites a 4-fold sum from variables (12)(34) to (13)(24) -/
theorem Finset.sum_4_rw {α : Type _} [AddCommMonoid α] (f : ℕ × ℕ × ℕ × ℕ → α) (n : ℕ) :
    (Finset.sum (Finset.range (n + 1)) fun k =>
        Finset.sum (Finset.range (k + 1)) fun a =>
          Finset.sum (Finset.range (n - k + 1)) fun c => f (a, k - a, c, n - k - c)) =
      Finset.sum (Finset.range (n + 1)) fun l =>
        Finset.sum (Finset.range (l + 1)) fun a =>
          Finset.sum (Finset.range (n - l + 1)) fun b => f (a, b, l - a, n - l - b) :=
  by
  rw [Finset.sum_sigma']
  rw [Finset.sum_sigma']
  rw [Finset.sum_sigma']
  rw [Finset.sum_sigma']
  let aux_i : (Σ i : Σ i : ℕ, ℕ, ℕ) → Σ i : Σ i : ℕ, ℕ, ℕ := fun ⟨⟨k, a⟩, c⟩ => ⟨⟨a + c, a⟩, k - a⟩
  have aux_hi :
    ∀ (a : Σ i : Σ i : ℕ, ℕ, ℕ)
      (ha :
        a ∈
          ((Finset.range (n + 1)).Sigma fun x : ℕ => Finset.range (x + 1)).Sigma
            fun a : Σ i : ℕ, ℕ => Finset.range (n - a.fst + 1)),
      (fun (x : Σ i : Σ i : ℕ, ℕ, ℕ)
              (hx :
                x ∈
                  ((Finset.range (n + 1)).Sigma fun a : ℕ => Finset.range (a + 1)).Sigma
                    fun a : Σ i : ℕ, ℕ => Finset.range (n - a.fst + 1)) =>
            aux_i x)
          a ha ∈
        ((Finset.range (n + 1)).Sigma fun a : ℕ => Finset.range (a + 1)).Sigma fun x : Σ i : ℕ, ℕ =>
          Finset.range (n - x.fst + 1) :=
    by
    rintro ⟨⟨k, a⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    simp_rw [aux_i, Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff]
    constructor; constructor
    · apply le_trans (add_le_add h.1.2 h.2) _
      rw [add_comm]; rw [Nat.sub_add_cancel h.1.1]
    · exact le_self_add
    · rw [add_comm a c]; rw [← Nat.sub_sub n c a]
      simp; rw [Nat.sub_add_cancel]
      rw [Nat.le_sub_iff_right]
      rw [Nat.le_sub_iff_right] at h ; rw [add_comm k c]; exact h.2
      exact h.1.1
      apply le_trans h.2; exact Nat.sub_le n k
      rw [Nat.le_sub_iff_right]
      rw [Nat.le_sub_iff_right] at h 
      apply Nat.le_of_add_le_add_right
      rw [add_assoc a c _]; rw [add_comm n _]
      exact add_le_add h.1.2 h.2
      exact h.1.1
      apply le_trans h.2 _; apply Nat.sub_le
  rw [Finset.sum_bij' (fun x hx => aux_i x) aux_hi _ (fun y hy => aux_i y) aux_hi _ _]
  · rintro ⟨⟨k, a⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    apply congr_arg
    dsimp [aux_i]
    simp only [Prod.mk.inj_iff]
    apply And.intro rfl
    apply And.intro rfl
    constructor
    · rw [add_comm a c]; rw [Nat.add_sub_cancel]
    · simp only [Nat.sub_sub]
      apply congr_arg₂ _ rfl
      rw [add_comm k c, add_comm a c, add_assoc]
      apply congr_arg₂ _ rfl
      rw [add_comm]
      rw [Nat.sub_add_cancel h.1.2]
  · rintro ⟨⟨k, a⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    simp_rw [aux_i]
    simp only [add_tsub_cancel_left, Sigma.mk.inj_iff, heq_iff_eq, eq_self_iff_true, and_true_iff]
    · rw [add_comm]; rw [Nat.sub_add_cancel h.1.2]
  · rintro ⟨⟨k, a⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h 
    simp_rw [aux_i]
    simp only [add_tsub_cancel_left, Sigma.mk.inj_iff, heq_iff_eq, eq_self_iff_true, and_true_iff]
    · rw [add_comm]; rw [Nat.sub_add_cancel h.1.2]
#align finset.sum_4_rw Finset.sum_4_rw

end FourFoldSums

theorem range_sym_prop {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).Sym m) :
    (Finset.sum (Finset.range (n + 1)) fun i => Multiset.count i ↑k) = m :=
  by
  simp only [Finset.mem_sym_iff] at hk 
  simp_rw [← k.prop]
  rw [← Multiset.toFinset_sum_count_eq ↑k]
  apply symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro i hi
    rw [Multiset.mem_toFinset, Sym.mem_coe] at hi 
    exact hk i hi
  · intro x hx
    rw [Finset.mem_sdiff, Multiset.mem_toFinset, Sym.mem_coe] at hx 
    simp only [Multiset.count_eq_zero, Sym.mem_coe]
    exact hx.2
  · intro x hk; rfl
#align range_sym_prop range_sym_prop

theorem range_sym_weighted_sum_le {m n : ℕ} (k : Sym ℕ m) (hk : k ∈ (Finset.range (n + 1)).Sym m) :
    ((Finset.range (n + 1)).Sum fun i => Multiset.count i ↑k * i) ≤ m * n :=
  by
  suffices :
    ∀ (i : ℕ) (hi : i ∈ Finset.range (n + 1)), Multiset.count i ↑k * i ≤ Multiset.count i ↑k * n
  apply le_trans (Finset.sum_le_sum this)
  rw [← Finset.sum_mul]
  rw [range_sym_prop hk]
  -- suffices
  intro i hi
  apply Nat.mul_le_mul_of_nonneg_left
  exact nat.lt_succ_iff.mp (finset.mem_range.mp hi)
#align range_sym_weighted_sum_le range_sym_weighted_sum_le

theorem sum_range_sym_mul_compl {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).Sym m) :
    (Finset.sum (Finset.range (n + 1)) fun i => Multiset.count i k * (n - i)) =
      m * n - Finset.sum (Finset.range (n + 1)) fun i => Multiset.count i k * i :=
  by
  suffices :
    (((Finset.range (n + 1)).Sum fun i => Multiset.count i ↑k * (n - i)) +
        (Finset.range (n + 1)).Sum fun i => Multiset.count i ↑k * i) =
      m * n
  rw [← this]; rw [Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add]
  have :
    ∀ (x : ℕ) (hx : x ∈ Finset.range (n + 1)),
      Multiset.count x ↑k * (n - x + x) = Multiset.count x ↑k * n :=
    by
    intro x hx
    rw [Nat.sub_add_cancel (nat.lt_succ_iff.mp (finset.mem_range.mp hx))]
  rw [Finset.sum_congr rfl this]
  rw [← Finset.sum_mul]
  rw [range_sym_prop hk]
#align sum_range_sym_mul_compl sum_range_sym_mul_compl

