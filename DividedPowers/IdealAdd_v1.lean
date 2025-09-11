/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowers.BasicLemmas
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.RingTheory.DividedPowers.DPMorphism

/-! # Alternative definition of divided powers on sums of ideals
This file is provided for comparison with `IdealAdd.lean`. Here we formalize the definition of the
divided power structure on `I + J` without relying on the theory of exponential power series.

To do that, we define `dpow : ℕ → A → A` as the function sending `n : ℕ` to
  `Function.extend (fun ⟨a, b⟩ => (a : A) + (b : A) : I × J → A)
    (fun ⟨a, b⟩ => Finset.sum (range (n + 1)) fun k => hI.dpow k (a : A) * hJ.dpow (n - k) (b : A))
    (Function.const A 0)`.

This requires us to show that this definition is independing of any choices, which we do in the
theorem `dpow_factorsThrough`. That is, if an element `c : A` can be expressed as a sum
`c = a + b = a' + b'` with `a, a' ∈ I`, `b, b' ∈ J` in multiples way, we need to show that
`dpow n c` does not depend on this choice of decomposition.

-/

open Finset

namespace DividedPowers

/- We need `A` to be a ring, until we can prove `dpow_factorsThrough` with semiring
 The better proof using the exponential module should work in the general case -/

variable {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {J : Ideal A}
  (hJ : DividedPowers J)

namespace IdealAdd_v1

/-- Some complicated numerical coefficients for the proof of ideal_add.dpow_comp -/
private def cnik := fun (n i : ℕ) (k : Multiset ℕ) =>
  ite (i = 0) (Nat.uniformBell (Multiset.count i k) n)
    (ite (i = n) (Nat.uniformBell (Multiset.count i k) n)
      ((Multiset.count i k).factorial * Nat.uniformBell (Multiset.count i k) i *
        Nat.uniformBell (Multiset.count i k) (n - i)))

/-- The divided power function on the sup of two ideals. -/
noncomputable def dpow : ℕ → A → A := fun n =>
  Function.extend (fun ⟨a, b⟩ => (a : A) + (b : A) : I × J → A)
    (fun ⟨a, b⟩ =>
      Finset.sum (range (n + 1)) fun k => hI.dpow k (a : A) * hJ.dpow (n - k) (b : A))
    (Function.const A 0)

/-- Independence on choices for `dpow` -/
theorem dpow_factorsThrough (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) :
    (fun (a, b) => Finset.sum (range (n + 1)) fun k => hI.dpow k (a : A) *
      hJ.dpow (n - k) (b : A)).FactorsThrough (fun ⟨a, b⟩ => (a : A) + (b : A) : I × J → A) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ H
  dsimp only at H ⊢
  -- Needs A to be a ring
  set c := a - a' with hc
  have haa' : a = a' + c := by simp only [hc, add_sub_cancel]
  have hbb' : b' = b + c := by rw [← sub_eq_iff_eq_add'.mpr H, haa']; ring
  have hcI : c ∈ I := sub_mem ha ha'
  have hcJ : c ∈ J := by rw [← sub_eq_iff_eq_add'.mpr hbb']; exact sub_mem hb' hb
  rw [haa', hbb']
  have Ha'c : ((range (n + 1)).sum fun k : ℕ => hI.dpow k (a' + c) * hJ.dpow (n - k) b) =
      (range (n + 1)).sum fun k : ℕ => (range (k + 1)).sum fun l : ℕ =>
        hI.dpow l a' * hJ.dpow (n - k) b * hI.dpow (k - l) c := by
    refine sum_congr rfl (fun k _ ↦ ?_)
    rw [hI.dpow_add' ha' hcI, sum_mul]
    exact sum_congr rfl (fun l _ ↦ by ring)
  have Hbc : ((range (n + 1)).sum fun k : ℕ => hI.dpow k a' * hJ.dpow (n - k) (b + c)) =
      (range (n + 1)).sum fun k : ℕ => (range (n - k + 1)).sum
        fun l : ℕ => hI.dpow k a' * hJ.dpow l b * hJ.dpow (n - k - l) c := by
    refine sum_congr rfl (fun k _ ↦ ?_)
    rw [hJ.dpow_add' hb hcJ, mul_sum]; ring_nf
  rw [Ha'c, sum_sigma', Hbc, sum_sigma']
  set s := (range (n + 1)).sigma fun a : ℕ => range (a + 1) with hs_def
  set i : ∀ x : Σ _ : ℕ, ℕ, x ∈ s → Σ _ : ℕ, ℕ := fun ⟨k, m⟩ _ => ⟨m, n - k⟩ with hi_def
  set t := (range (n + 1)).sigma fun a : ℕ => range (n - a + 1) with ht_def
  set j : ∀ y : Σ _ : ℕ, ℕ, y ∈ t → Σ _ : ℕ, ℕ := fun ⟨k, m⟩ _ => ⟨n - m, k⟩ with hj_def
  rw [sum_bij' i j _ _ _ _]
  · rintro ⟨k, m⟩ h
    apply congr_arg₂ _ rfl
    suffices h : n - m - (n - k) = k - m by
      rw [h]
      apply hIJ
      exact ⟨hcI, hcJ⟩
    rw [Nat.sub_sub, add_comm, ← Nat.sub_sub, Nat.sub_sub_self ?_]
    simp only [hs_def, mem_sigma, mem_range] at h
    exact Nat.le_of_lt_succ h.1
  · rintro ⟨k, m⟩ h
    simp only [hs_def, ht_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h ⊢
    exact ⟨le_trans h.2 h.1, tsub_le_tsub_left h.2 _⟩
  · rintro ⟨k, m⟩ h
    simp only [hs_def, ht_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h ⊢
    apply And.intro (Nat.sub_le _ _)
    rw [Nat.le_sub_iff_add_le] at h ⊢
    rw [add_comm]; exact h.2
    exact le_trans (Nat.le_add_right _ _) h.2
    exact h.1
  · rintro ⟨k, m⟩ h
    simp only [hs_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp only [i, hj_def, Sigma.mk.inj_iff, heq_eq_eq, and_true]
    exact Nat.sub_sub_self h.1
  · rintro ⟨u, v⟩ h
    simp only [ht_def, mem_sigma, mem_range, Nat.lt_succ_iff] at h
    simp only [j, hi_def, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    exact Nat.sub_sub_self (le_trans h.2 (Nat.sub_le n u))

theorem dpow_eq (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ} {a b : A}
    (ha : a ∈ I) (hb : b ∈ J) : dpow hI hJ n (a + b) =
      Finset.sum (range (n + 1)) fun k => hI.dpow k a * hJ.dpow (n - k) b := by
  rw [IdealAdd_v1.dpow, (dpow_factorsThrough hI hJ hIJ n).extend_apply _ (⟨⟨a, ha⟩, ⟨b, hb⟩⟩ : I × J)]

private theorem dpow_eq_of_mem_left' (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ}
    {x : A} (hx : x ∈ I) : dpow hI hJ n x = hI.dpow n x := by
  rw [← add_zero x, dpow_eq hI hJ hIJ hx J.zero_mem]
  · rw [sum_eq_single n _ (fun hn ↦ absurd (self_mem_range_succ n) hn)]
    · simp only [le_refl, tsub_eq_zero_of_le, add_zero]
      rw [hJ.dpow_zero J.zero_mem, mul_one]
    · intro b hb hb'
      rw [hJ.dpow_eval_zero, mul_zero]
      rw [mem_range, Nat.lt_succ_iff] at hb
      omega

private theorem dpow_eq_of_mem_right' (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ}
    {x : A} (hx : x ∈ J) : dpow hI hJ n x = hJ.dpow n x := by
  rw [← zero_add x, dpow_eq hI hJ hIJ I.zero_mem hx, sum_eq_single 0]
  · simp only [Nat.sub_zero, zero_add, hI.dpow_zero I.zero_mem, one_mul]
  · intro b _ hb'
    rw [hI.dpow_eval_zero, zero_mul]; exact hb'
  · exact fun hn ↦ absurd (mem_range.mpr n.zero_lt_succ) hn

theorem dpow_zero (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    ∀ {x : A} (_ : x ∈ I + J), dpow hI hJ 0 x = 1 := by
  intro x
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [dpow_eq hI hJ hIJ ha hb]
  simp only [zero_add, range_one, zero_le, tsub_eq_zero_of_le, sum_singleton]
  rw [hI.dpow_zero ha, hJ.dpow_zero hb, mul_one]

theorem dpow_mul (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {m n : ℕ} {x : A} :
    x ∈ I + J → dpow hI hJ m x * dpow hI hJ n x = ↑((m + n).choose m) * dpow hI hJ (m + n) x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [dpow_eq hI hJ hIJ ha hb, ← Nat.sum_antidiagonal_eq_sum_range_succ
    fun i j => hI.dpow i a * hJ.dpow j b, dpow_eq hI hJ hIJ ha hb,
    ← Nat.sum_antidiagonal_eq_sum_range_succ fun k l => hI.dpow k a * hJ.dpow l b, sum_mul]
  simp_rw [mul_sum, ← sum_product']
  have hf : ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      hI.dpow x.1.1 a * hJ.dpow x.1.2 b * (hI.dpow x.2.1 a * hJ.dpow x.2.2 b) =
        (x.1.1 + x.2.1).choose x.1.1 * (x.1.2 + x.2.2).choose x.1.2 *
            hI.dpow (x.1.1 + x.2.1) a * hJ.dpow (x.1.2 + x.2.2) b := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    dsimp only
    rw [mul_assoc, ← mul_assoc (hJ.dpow j b), mul_comm (hJ.dpow j b), mul_assoc, hJ.mul_dpow hb,
      ← mul_assoc, hI.mul_dpow ha]
    ring
  rw [sum_congr rfl fun x _ => hf x]
  set s : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := fun x => ⟨x.1.1 + x.2.1, x.1.2 + x.2.2⟩ with hs_def
  have hs : ∀ x ∈ antidiagonal m ×ˢ antidiagonal n, s x ∈ antidiagonal (m + n) := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ h
    simp only [mem_antidiagonal, mem_product] at h ⊢
    rw [add_assoc, ← add_assoc k j l, add_comm k _, add_assoc, h.2, ← add_assoc, h.1]
  rw [← sum_fiberwise_of_maps_to hs]
  have hs' : ((antidiagonal (m + n)).sum fun y : ℕ × ℕ => ((antidiagonal m ×ˢ antidiagonal n).filter
      (fun x : (ℕ × ℕ) × ℕ × ℕ => (fun x : (ℕ × ℕ) × ℕ × ℕ => s x) x = y)).sum
        (fun x : (ℕ × ℕ) × ℕ × ℕ => ↑((x.1.1 + x.2.1).choose x.1.1) *
          ↑((x.1.2 + x.2.2).choose x.1.2) * hI.dpow (x.1.1 + x.2.1) a *
          hJ.dpow (x.1.2 + x.2.2) b)) =
      (antidiagonal (m + n)).sum (fun y : ℕ × ℕ => (((antidiagonal m ×ˢ antidiagonal n).filter
        (fun x : (ℕ × ℕ) × ℕ × ℕ => (fun x : (ℕ × ℕ) × ℕ × ℕ => s x) x = y)).sum
          (fun x : (ℕ × ℕ) × ℕ × ℕ => (y.fst.choose x.1.1) * (y.snd.choose x.1.2)) *
          hI.dpow y.fst a * hJ.dpow y.snd b)) := by
    apply sum_congr rfl
    rintro ⟨u, v⟩ _
    simp only [Nat.cast_sum, Nat.cast_mul, sum_mul]
    apply sum_congr rfl
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hx
    simp only [hs_def, mem_product, mem_antidiagonal, mem_filter, Prod.mk.injEq] at hx
    rw [hx.2.1, hx.2.2]
  rw [hs', dpow_eq hI hJ hIJ ha hb, ← Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
    hI.dpow i a * hJ.dpow j b, mul_sum]
  apply sum_congr rfl
  rintro ⟨u, v⟩ h
  rw [← mul_assoc]
  apply congr_arg₂ _ _ rfl
  apply congr_arg₂ _ _ rfl
  apply congr_arg
  simp only [mem_antidiagonal] at h
  simp only [hs_def, Prod.mk.injEq]
  rw [rewriting_4_fold_sums h.symm (fun x => u.choose x.fst * v.choose x.snd) rfl _]
  · rw [← Nat.add_choose_eq, h]
  · intro x h
    rcases h with h | h <;>
      · simp only [Nat.choose_eq_zero_of_lt h, zero_mul, mul_zero]

theorem dpow_mem (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ} (hn : n ≠ 0)
    {x : A} (hx : x ∈ I + J) : dpow hI hJ n x ∈ I + J := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hI hJ hIJ ha hb]
  refine Submodule.sum_mem (I ⊔ J) (fun k _ ↦ ?_)
  by_cases hk0 : k = 0
  · exact hk0 ▸ Submodule.mem_sup_right (J.mul_mem_left _ (hJ.dpow_mem hn hb))
  · exact Submodule.mem_sup_left (I.mul_mem_right _ (hI.dpow_mem hk0 ha))

theorem dpow_smul (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ} {c x : A}
    (hx : x ∈ I + J) : dpow hI hJ n (c * x) = c ^ n * dpow hI hJ n x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hI hJ hIJ ha hb, mul_add, dpow_eq hI hJ hIJ (I.mul_mem_left c ha)
    (J.mul_mem_left c hb), mul_sum]
  refine sum_congr rfl (fun k hk ↦ ?_)
  simp only [mem_range, Nat.lt_succ_iff] at hk
  rw [hI.dpow_mul ha, hJ.dpow_mul hb]
  simp only [← mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  rw [mul_comm, ← mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  rw [← pow_add, Nat.sub_add_cancel hk]

theorem dpow_add' (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ} {x y : A}
    (hx : x ∈ I + J) (hy : y ∈ I + J) :
    dpow hI hJ n (x + y) =
      Finset.sum (range (n + 1)) fun k => dpow hI hJ k x * dpow hI hJ (n - k) y := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hy
  rw [add_add_add_comm a b a' b', dpow_eq hI hJ hIJ (I.add_mem ha ha') (J.add_mem hb hb')]
  let f : ℕ × ℕ × ℕ × ℕ → A := fun ⟨i, j, k, l⟩ =>
    hI.dpow i a * hI.dpow j a' * hJ.dpow k b * hJ.dpow l b'
  have hf1 : ∀ k ∈ range (n + 1), hI.dpow k (a + a') * hJ.dpow (n - k) (b + b') =
      (range (k + 1)).sum fun i =>(range (n - k + 1)).sum fun l =>
        hI.dpow i a * hI.dpow (k - i) a' * hJ.dpow l b * hJ.dpow (n - k - l) b' := fun k _ ↦ by
    rw [hI.dpow_add' ha ha', hJ.dpow_add' hb hb', sum_mul]
    refine sum_congr rfl (fun _ _ ↦ ?_)
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ ↦ by ring)
  have hf2 : ∀ k ∈ range (n + 1), dpow hI hJ k (a + b) * dpow hI hJ (n - k) (a' + b') =
      (range (k + 1)).sum fun i => (range (n - k + 1)).sum fun l =>
        hI.dpow i a * hI.dpow l a' * hJ.dpow (k - i) b * hJ.dpow (n - k - l) b' := fun k _ ↦ by
    rw [dpow_eq hI hJ hIJ ha hb, dpow_eq hI hJ hIJ ha' hb', sum_mul]
    refine sum_congr rfl (fun _ _ ↦ ?_)
    rw [mul_sum]
    exact sum_congr rfl (fun _ _ ↦ by ring)
  rw [sum_congr rfl hf1, sum_congr rfl hf2, sum_4_rw f n]

theorem dpow_add (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ} {x y : A}
    (hx : x ∈ I + J) (hy : y ∈ I + J) : dpow hI hJ n (x + y) =
      (antidiagonal n).sum fun (k, l) => dpow hI hJ k x * dpow hI hJ l y := by
  simp only [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact dpow_add' hI hJ hIJ hx hy

/-- Prove the `dpow_comp` axiom for the ideal `I ⊔ J`, assuming agreement on `I ⊓ J` , -/
theorem dpow_comp_aux (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {m n : ℕ}
   (hn : n ≠ 0) {a : A} (ha : a ∈ I) {b : A} (hb : b ∈ J) :
    dpow hI hJ m (dpow hI hJ n (a + b)) = Finset.sum (range (m * n + 1)) fun p : ℕ =>
      ((filter (fun l : Sym ℕ m => ((range (n + 1)).sum fun i => Multiset.count i ↑l * i) = p)
        ((range (n + 1)).sym m)).sum fun x : Sym ℕ m =>
          (((range (n + 1)).prod fun i : ℕ => cnik n i ↑x) *
      Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑x * i) *
      Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑x * (n - i)) *
      hI.dpow p a * hJ.dpow (m * n - p) b := by
  rw [dpow_eq hI hJ hIJ ha hb, dpow_sum' (dpow := dpow hI hJ)]
  · have L1 : ∀ (k : Sym ℕ m) (i : ℕ) (_ : i ∈ range (n + 1)),
        dpow hI hJ (Multiset.count i ↑k) (hI.dpow i a * hJ.dpow (n - i) b) = cnik n i ↑k *
          hI.dpow (Multiset.count i ↑k * i) a * hJ.dpow (Multiset.count i ↑k * (n - i)) b := by
      intro k i hi
      simp only [cnik]
      by_cases hi2 : i = n
      · rw [hi2, Nat.sub_self, if_neg hn, if_pos rfl]
        simp only [hJ.dpow_zero hb, mul_one, mul_zero]
        rw [dpow_eq_of_mem_left' hI hJ hIJ (hI.dpow_mem hn ha), hI.dpow_comp hn ha]
      · have hi2' : n - i ≠ 0 := by
          intro h; apply hi2
          rw [mem_range, Nat.lt_succ_iff] at hi
          rw [← Nat.sub_add_cancel hi, h, zero_add]
        by_cases hi1 : i = 0
        · rw [hi1, hI.dpow_zero ha, Nat.sub_zero, one_mul, if_pos rfl,
            dpow_eq_of_mem_right' hI hJ hIJ (hJ.dpow_mem hn hb), hJ.dpow_comp hn hb, mul_zero,
            hI.dpow_zero ha, mul_one]
        -- i ≠ 0  and i ≠ n
        · rw [if_neg hi1, if_neg hi2, mul_comm, dpow_smul hI hJ hIJ
            (Submodule.mem_sup_left (hI.dpow_mem hi1 ha)), mul_comm, dpow_eq_of_mem_left' hI hJ hIJ
            (hI.dpow_mem hi1 ha), ← hJ.factorial_mul_dpow_eq_pow (hJ.dpow_mem hi2' hb),
            hI.dpow_comp hi1 ha, hJ.dpow_comp hi2' hb]
          simp only [← mul_assoc]
          apply congr_arg₂ _ _ rfl
          simp only [mul_assoc]
          rw [mul_comm (hI.dpow _ a)]
          simp only [← mul_assoc]
          apply congr_arg₂ _ _ rfl
          simp only [Nat.cast_mul]
          apply congr_arg₂ _ _ rfl
          rw [mul_comm]
    set φ : Sym ℕ m → ℕ := fun k => (range (n + 1)).sum fun i => Multiset.count i ↑k * i with hφ_def
    suffices hφ : ∀ k : Sym ℕ m, k ∈ (range (n + 1)).sym m → φ k ∈ range (m * n + 1) by
      rw [← sum_fiberwise_of_maps_to hφ _]
      suffices L4 : ∀ (p : ℕ) (_ : p ∈ range (m * n + 1)),
          ((filter (fun x : Sym ℕ m => (fun k : Sym ℕ m => φ k) x = p) ((range (n + 1)).sym m)).sum
              fun x : Sym ℕ m => (range (n + 1)).prod fun i : ℕ =>
                dpow hI hJ (Multiset.count i ↑x) (hI.dpow i a * hJ.dpow (n - i) b)) =
            (filter (fun x : Sym ℕ m => (fun k : Sym ℕ m => φ k) x = p) ((range (n + 1)).sym m)).sum
              fun k : Sym ℕ m => ((range (n + 1)).prod fun i : ℕ => ↑(cnik n i ↑k)) *
                      ↑(Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑k * i) *
                    ↑(Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑k * (n - i)) *
              hI.dpow p a * hJ.dpow (m * n - p) b by
          simp only [sum_congr rfl L4, Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, sum_mul]
          congr
      intro p _
      apply sum_congr rfl
      intro k hk
      rw [mem_filter] at hk
      rw [prod_congr rfl (L1 k), prod_mul_distrib, prod_mul_distrib,
        hI.prod_dpow ha, hJ.prod_dpow hb]
      simp only [mul_assoc]; apply congr_arg₂ _ rfl
      apply congr_arg₂ _ rfl
      rw [sum_range_sym_mul_compl hk.1]
      simp only [← mul_assoc]
      simp only [mem_sym_iff, mem_range, hφ_def] at hk
      rw [hk.2]
      apply congr_arg₂ _ _ rfl
      rw [mul_comm]
    -- hφ
    intro k hk
    simp only [φ, mem_range, Nat.lt_succ_iff, range_sym_weighted_sum_le hk]
  . -- dpow_zero
    intro x hx
    rw [dpow_zero hI hJ hIJ hx]
  . -- dpow_add
    intro n x y hx hy
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, dpow_add' hI hJ hIJ hx hy]
  · -- dpow_eval_zero
    intro n hn
    rw [dpow_eq_of_mem_left' hI hJ hIJ I.zero_mem, dpow_eval_zero hI hn]
  · intro i _
    by_cases hi0 : i = 0
    · exact hi0 ▸ Submodule.mem_sup_right (J.mul_mem_left _ (hJ.dpow_mem hn hb))
    · apply Submodule.mem_sup_left (I.mul_mem_right _ (hI.dpow_mem hi0 ha))

open BigOperators Polynomial

theorem dpow_comp_coeffs {m n p : ℕ} (hn : n ≠ 0) (hp : p ≤ m * n) :
  Nat.uniformBell m n =
    (filter (fun l : Sym ℕ m => ((range (n + 1)).sum fun i : ℕ => Multiset.count i ↑l * i) = p)
      ((range (n + 1)).sym m)).sum fun x : Sym ℕ m =>
        ((range (n + 1)).prod fun i : ℕ => cnik n i ↑x) *
          ((Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑x * i) *
            Nat.multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑x * (n - i)) := by
  classical
  rw [← mul_left_inj' (pos_iff_ne_zero.mp (Nat.choose_pos hp))]
  apply @Nat.cast_injective ℚ
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_prod]
  conv_lhs => rw [← Polynomial.coeff_X_add_one_pow ℚ (m * n) p]
  let A := ℚ[X]
  let I : Ideal A := ⊤
  let hI : DividedPowers I := RatAlgebra.dividedPowers ⊤
  let hII : ∀ (n : ℕ), ∀ a ∈ I ⊓ I, hI.dpow n a = hI.dpow n a := fun _ _ _ => rfl
  let h1 : (1 : A) ∈ I := Submodule.mem_top
  let hX : X ∈ I := Submodule.mem_top
  rw [← hI.factorial_mul_dpow_eq_pow Submodule.mem_top, ← Polynomial.coeff_C_mul,
    ← mul_assoc, mul_comm (C ((Nat.uniformBell m n) : ℚ)), mul_assoc, C_eq_natCast,
    ← hI.dpow_comp hn Submodule.mem_top, ← dpow_eq_of_mem_left' hI hI hII Submodule.mem_top,
    ← dpow_eq_of_mem_left' hI hI hII Submodule.mem_top, dpow_comp_aux hI hI hII hn hX h1,
    ← C_eq_natCast, mul_sum, finset_sum_coeff]
  simp only [hI, RatAlgebra.dpow_eq_inv_fact_smul _ _ Submodule.mem_top, map_natCast,
    Ring.inverse_eq_inv', Algebra.mul_smul_comm, one_pow, mul_one, coeff_smul, coeff_natCast_mul,
    smul_eq_mul]
  simp only [← Nat.cast_prod, ← Nat.cast_mul, ← Nat.cast_sum]
  rw [sum_eq_single p]
  · conv_lhs =>
      rw [coeff_natCast_mul, coeff_X_pow, if_pos, mul_one, ← mul_assoc, mul_comm]
      simp only [mul_assoc]
      rw [mul_comm]
    simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_prod, sum_mul]
    apply sum_congr rfl
    intro x _
    simp only [mul_assoc]
    congr
    ring_nf
    simp only [mul_assoc]
    rw [inv_mul_eq_iff_eq_mul₀, inv_mul_eq_iff_eq_mul₀, ← Nat.choose_mul_factorial_mul_factorial hp]
    simp only [Nat.cast_mul]
    ring
    all_goals
      simp only [ne_eq, Nat.cast_eq_zero]
      exact Nat.factorial_ne_zero _
  · intro b _ hb
    rw [coeff_natCast_mul, coeff_X_pow, if_neg hb.symm]
    simp only [mul_zero]
  · intro hp'
    simp only [mem_range, Nat.lt_succ_iff] at hp'
    contradiction

theorem dpow_comp (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {m n : ℕ} {x : A}
    (hn : n ≠ 0) (hx : x ∈ I + J) :
    dpow hI hJ m (dpow hI hJ n x) = ↑(Nat.uniformBell m n) * dpow hI hJ (m * n) x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_comp_aux hI hJ hIJ hn ha hb,
    dpow_add' hI hJ hIJ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [dpow_eq_of_mem_left' hI hJ hIJ ha, dpow_eq_of_mem_right' hI hJ hIJ hb]
  simp only [mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  -- it remains to check coefficients
  rw [dpow_comp_coeffs hn (Nat.lt_succ_iff.mp (mem_range.mp hp))]

theorem dpow_null {n : ℕ} {x : A} (hx : x ∉ I + J) : dpow hI hJ n x = 0 := by
  simp only [dpow, Function.const_zero]
  rw [Function.extend_apply', Pi.zero_apply]
  rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, h⟩
  exact hx (h ▸ Submodule.add_mem_sup ha hb)

theorem dpow_one (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {x : A}
    (hx : x ∈ I + J) : dpow hI hJ 1 x = x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hI hJ hIJ ha hb]
  suffices h : range (1 + 1) = {0, 1} by
    simp only [h, sum_insert, mem_singleton, Nat.zero_ne_one, not_false_iff, tsub_zero,
      sum_singleton, tsub_self, hI.dpow_zero ha, hI.dpow_one ha, hJ.dpow_zero hb, hJ.dpow_one hb]
    ring
  · rw [range_succ, range_one]; ext k; simp; exact or_comm

/-- The divided power structure on the ideal `I + J`, given that `hI` and `hJ` agree on `I ⊓ J`. -/
noncomputable def dividedPowers {J : Ideal A} (hJ : DividedPowers J)
    (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    DividedPowers (I + J) where
  dpow           := dpow hI hJ
  dpow_null      := dpow_null hI hJ
  dpow_zero      := dpow_zero hI hJ hIJ
  dpow_one       := dpow_one hI hJ hIJ
  dpow_mem hn hx := dpow_mem hI hJ hIJ hn hx
  dpow_add       := dpow_add hI hJ hIJ
  dpow_mul       := dpow_smul hI hJ hIJ
  mul_dpow       := dpow_mul hI hJ hIJ
  dpow_comp      := dpow_comp hI hJ hIJ

theorem dpow_unique (hsup : DividedPowers (I + J))
    (hI' : ∀ {n : ℕ}, ∀ a ∈ I, hI.dpow n a = hsup.dpow n a)
    (hJ' : ∀ {n : ℕ}, ∀ b ∈ J, hJ.dpow n b = hsup.dpow n b) :
    let hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a := fun n a ha => by
      rw [Submodule.mem_inf] at ha; rw [hI' _ ha.1, hJ' _ ha.2]
    hsup = dividedPowers hI hJ hIJ := by
  intro hIJ
  refine hsup.ext _ (fun n x hx ↦ ?_)
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp only [hsup.dpow_add' (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb),
    IdealAdd_v1.dividedPowers, dpow_eq hI hJ hIJ ha hb]
  exact sum_congr rfl (fun k _ ↦ congr_arg₂ (· * ·) (hI' a ha).symm (hJ' b hb).symm)

lemma isDPMorphism_left (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    hI.IsDPMorphism (IdealAdd_v1.dividedPowers hI hJ hIJ) (RingHom.id A):=
  ⟨by simp only [Ideal.map_id]; exact le_sup_left, fun _ ↦ dpow_eq_of_mem_left' hI hJ hIJ⟩

lemma isDPMorphism_right (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    hJ.IsDPMorphism (IdealAdd_v1.dividedPowers hI hJ hIJ) (RingHom.id A) :=
  ⟨by simp only [Ideal.map_id]; exact le_sup_right, fun _ ↦ dpow_eq_of_mem_right' hI hJ hIJ⟩

theorem dpow_eq_of_mem_left (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ}
    {x : A} (hx : x ∈ I) :
      (IdealAdd_v1.dividedPowers hI hJ hIJ).dpow n x = hI.dpow n x :=
  dpow_eq_of_mem_left' hI hJ hIJ hx

theorem dpow_eq_of_mem_right (hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {n : ℕ}
    {x : A} (hx : x ∈ J) :
    (IdealAdd_v1.dividedPowers hI hJ hIJ).dpow n x = hJ.dpow n x :=
  dpow_eq_of_mem_right' hI hJ hIJ hx

end IdealAdd_v1

end DividedPowers
