/-
! This file was ported from Lean 3 source module basic_lemmas
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Finset.Sym


/-

section Classical

open scoped Classical

-- This function now exists in mathlib
-- as `Function.FactorsThrough.extend_apply`
-- where `g.FactorsThrough f` is
-- `∀ a b : α, f a = f b → g a = g b)`


theorem Function.extend_apply_first {α β γ : Type _} (f : α → β) (g : α → γ) (e' : β → γ)
    (hf : ∀ a b : α, f a = f b → g a = g b) (a : α) : Function.extend f g e' (f a) = g a :=
  by
  simp only [Function.extend_def, dif_pos, exists_apply_eq_apply]
  apply hf
  exact Classical.choose_spec (exists_apply_eq_apply f a)
#align function.extend_apply_first Function.extend_apply_first

end Classical

-/

open BigOperators

section FourFoldSums

/- This lemma is awkward and mathematically obvious,
just rewrite the sum using the variable x which determines y, z, t.
However, one of its points is to reduce a 4-fold sum to a 2-fold sum.  -/

/-- The sum of f(x, y) on x + y = m and z + t = n and x + z = u and y + t = v
  is equal to the sum of  f(x, y) on x + y = m
  provided f (x, y) vanishes if x > u or y > v.
-/
theorem rewriting_4_fold_sums {α : Type _} [CommSemiring α] {m n u v : ℕ}
  (h : m + n = u + v) (f : ℕ × ℕ → α) {g : (ℕ × ℕ) × ℕ × ℕ → α}
  (hgf : g = fun x => f (x.fst.fst, x.fst.snd))
  (hf : ∀ x : ℕ × ℕ, u < x.fst ∨ v < x.snd → f x = 0) :
  (Finset.filter
    (fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
      (Finset.antidiagonal m ×ˢ Finset.antidiagonal n)).sum g =
    (Finset.antidiagonal m).sum f := by
  -- let q := fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst
  have hq :∀ x ∈ Finset.filter
    (fun x : (ℕ × ℕ) × ℕ × ℕ => x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v)
      (Finset.antidiagonal m ×ˢ Finset.antidiagonal n),
    x.fst ∈ Finset.antidiagonal m := by
    intro x; simp; intro h'; simp [h']
  rw [← Finset.sum_fiberwise_of_maps_to hq]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij; simp only [Finset.mem_antidiagonal] at hij
  rw [Finset.sum_filter]; rw [Finset.sum_filter]
  simp_rw [← ite_and]
  suffices hf' :
    ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j)) (g x) 0 =
        ite ((x.fst.fst + x.snd.fst = u ∧ x.fst.snd + x.snd.snd = v) ∧ x.fst = (i, j)) 1 0 *
          f ⟨i, j⟩ by
    rw [Finset.sum_congr rfl fun x _ => hf' x, ← Finset.sum_mul]
    by_cases hij' : i ≤ u ∧ j ≤ v
    · conv_rhs => rw [← one_mul (f ⟨i, j⟩)]
      apply congr_arg₂ _ _ rfl
      rw [Finset.sum_eq_single (⟨⟨i, j⟩, ⟨u - i, v - j⟩⟩ : (ℕ × ℕ) × ℕ × ℕ)]
      simp only [Nat.add_sub_of_le hij'.1, Nat.add_sub_of_le hij'.2, eq_self_iff_true, and_self_iff,
        if_true]
      · rintro ⟨⟨x, y⟩, ⟨z, t⟩⟩ hb hb'; rw [if_neg]; intro hb''
        simp only [Finset.mem_product, Finset.mem_antidiagonal] at hb
        simp only [Ne.def, Prod.mk.inj_iff, not_and, and_imp] at hb'
        simp only [Prod.mk.inj_iff] at hb''
        specialize hb' hb''.2.1 hb''.2.2
        rw [hb''.2.1, hb''.2.2] at hb
        apply hb'
        apply Nat.add_left_cancel; rw [Nat.add_sub_of_le hij'.1, ← hb''.2.1, hb''.1.1]
        apply Nat.add_left_cancel; rw [Nat.add_sub_of_le hij'.2, ← hb''.2.2, hb''.1.2]
      · intro hb; rw [if_neg]; intro hb'; apply hb
        simp only [eq_self_iff_true, and_true_iff] at hb'
        simp only [Finset.mem_product, Finset.mem_antidiagonal]
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


/- TODO : There should be some general rewriting pattern
for sums indexed by finset.nat_tuple_antidiagonal
This one would first rewrite to
(finset.nat_tuple_antidiagonal 4 n).sum (λ x, f(x0, x1, x2, x3))
and then one would apply the permutation (13)(24) -/

open BigOperators

/-- Rewrites a 4-fold sum from variables (12)(34) to (13)(24) -/
theorem Finset.sum_4_rw {α : Type _} [AddCommMonoid α]
  (f : ℕ × ℕ × ℕ × ℕ → α) (n : ℕ) :
  (Finset.sum (Finset.range (n + 1)) fun k =>
    Finset.sum (Finset.range (k + 1)) fun a =>
      Finset.sum (Finset.range (n - k + 1)) fun c => f (a, k - a, c, n - k - c)) =
    Finset.sum (Finset.range (n + 1)) fun l =>
      Finset.sum (Finset.range (l + 1)) fun a =>
        Finset.sum (Finset.range (n - l + 1)) fun b => f (a, b, l - a, n - l - b) := by
  rw [Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma', Finset.sum_sigma']
  let φ : (Σ (_ : Σ (_ : ℕ), ℕ), ℕ) → (Σ (_ : Σ (_ : ℕ), ℕ), ℕ) :=
    fun ⟨⟨k, a⟩, c⟩ => ⟨⟨a + c, a⟩, k - a⟩
  --suffices h1 : (hi : ∀ ((_ : (_ : ℕ) × ℕ) × ℕ) ha, i a ha ∈ t)
  --suffices h2 : _
  have h1 : ∀ (a : (_ : (_ : ℕ) × ℕ) × ℕ) (ha : a ∈ Finset.sigma
      (Finset.sigma (range (n + 1)) fun l => range (l + 1)) fun x => range (n - x.fst + 1)),
      (fun m _ => φ m) a ha ∈ Finset.sigma (Finset.sigma (range (n + 1))
        fun k => range (k + 1)) fun x => range (n - x.fst + 1) := by
    rintro ⟨⟨k, a⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h
    simp_rw [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff]
    constructor; constructor
    · apply le_trans (add_le_add h.1.2 h.2) _
      rw [add_comm]; rw [Nat.sub_add_cancel h.1.1]
    · exact le_self_add
    · rw [add_comm a c]; rw [← Nat.sub_sub n c a]
      apply Nat.sub_le_sub_right
      rw [Nat.le_sub_iff_add_le]
      rw [Nat.le_sub_iff_add_le h.1.1, add_comm] at h
      exact h.2
      exact le_trans h.2 (Nat.sub_le n k)

  have h2 : ∀ (a : (_ : (_ : ℕ) × ℕ) × ℕ) (ha : a ∈ Finset.sigma (Finset.sigma (range (n + 1))
      fun k => range (k + 1)) fun x => range (n - x.fst + 1)),
      (fun m _ => φ m) ((fun m _ => φ m) a ha) ((fun m _ => φ m) a ha ∈
        Finset.sigma (Finset.sigma (range (n + 1)) fun k => range (k + 1))
          fun x => range (n - x.fst + 1)) =
    a := by
    rintro ⟨⟨k, a⟩, c⟩ h
    simp only [Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff] at h
    simp only [add_tsub_cancel_left, Sigma.mk.inj_iff, heq_eq_eq, and_true]
    refine add_tsub_cancel_of_le h.1.2

  refine Finset.sum_bij' (fun m _ => φ m) (fun m _ => φ m) h1 h1 h2 h2 ?_
  · rintro ⟨⟨k, a⟩, c⟩ h
    simp only [mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp only [Nat.add_sub_self_left a c, Nat.sub_sub,
      add_comm (a + c), ← add_assoc, Nat.sub_add_cancel h.1.2]
#align finset.sum_4_rw Finset.sum_4_rw

end FourFoldSums

theorem range_sym_prop {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (Finset.range (n + 1)) fun i => Multiset.count i k) = m :=
  by
  simp only [Finset.mem_sym_iff] at hk
  simp_rw [← k.prop]
  rw [← Multiset.toFinset_sum_count_eq]
  apply symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro i hi
    simp only [Sym.val_eq_coe, Multiset.mem_toFinset, Sym.mem_coe] at hi
    exact hk i hi
  · intro x hx
    simp only [Sym.val_eq_coe, Finset.mem_sdiff, Finset.mem_range, Multiset.mem_toFinset, Sym.mem_coe] at hx
    simp only [Multiset.count_eq_zero, Sym.mem_coe]
    exact hx.2
  · intro x _; rfl
#align range_sym_prop range_sym_prop

theorem range_sym_weighted_sum_le {m n : ℕ} {k : Sym ℕ m}
    (hk : k ∈ (Finset.range (n + 1)).sym m) :
    ((Finset.range (n + 1)).sum fun i => Multiset.count i k * i) ≤ m * n := by
  suffices h : ∀ i ∈ Finset.range (n + 1), Multiset.count i k * i ≤ Multiset.count i k * n by
    apply le_trans (Finset.sum_le_sum h)
    rw [← Finset.sum_mul, range_sym_prop hk]
  intro i hi
  apply Nat.mul_le_mul_left
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
#align range_sym_weighted_sum_le range_sym_weighted_sum_le

theorem sum_range_sym_mul_compl {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (Finset.range (n + 1)) fun i => Multiset.count i k * (n - i)) =
      m * n - Finset.sum (Finset.range (n + 1)) fun i => Multiset.count i k * i := by
  suffices h : (((Finset.range (n + 1)).sum fun i => Multiset.count i k * (n - i)) +
        (Finset.range (n + 1)).sum fun i => Multiset.count i k * i) = m * n by
    rw [← h, Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add]
  have :
    ∀ x ∈ Finset.range (n + 1),
      Multiset.count x ↑k * (n - x + x) = Multiset.count x ↑k * n := by
    intro x hx
    rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, range_sym_prop hk]
#align sum_range_sym_mul_compl sum_range_sym_mul_compl
