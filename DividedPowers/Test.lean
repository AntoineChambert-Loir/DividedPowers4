/-
Copyright (c) 2022 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
--import Mathlib.Data.Finset.Sym
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Algebra.Ring.Defs

open BigOperators --Finset

namespace Finset

-- TODO: we need to rename these lemmas before PRing them.

open Multiset

-- Mathlib.Algebra.BigOperators.Sym
theorem range_sym_prop {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (range (n + 1)) fun i => count i k) = m := by
  simp_rw [← k.prop, ← toFinset_sum_count_eq, eq_comm]
  apply sum_subset_zero_on_sdiff _ _ (fun _ _ ↦ rfl)
  · intro i hi
    simp only [Sym.val_eq_coe, mem_toFinset, Sym.mem_coe] at hi
    exact mem_sym_iff.mp hk i hi
  · intro _ hx
    simp only [Sym.val_eq_coe, mem_sdiff, Finset.mem_range, mem_toFinset, Sym.mem_coe] at hx
    simp only [count_eq_zero, Sym.mem_coe]
    exact hx.2

theorem range_sym_weighted_sum_le {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    ((Finset.range (n + 1)).sum fun i => count i k * i) ≤ m * n := by
  suffices h : ∀ i ∈ Finset.range (n + 1), count i k * i ≤ count i k * n by
    exact le_trans (sum_le_sum h) (by rw [← sum_mul, range_sym_prop hk])
  exact fun _ hi ↦ Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

--#find_home! range_sym_weighted_sum_le

-- Mathlib.Data.Multiset.Count ??
theorem sum_range_sym_mul_compl {m n : ℕ} {k : Sym ℕ m} (hk : k ∈ (Finset.range (n + 1)).sym m) :
    (Finset.sum (range (n + 1)) fun i => count i k * (n - i)) =
      m * n - Finset.sum (range (n + 1)) fun i => count i k * i := by
  suffices h : (((Finset.range (n + 1)).sum fun i => count i k * (n - i)) +
        (Finset.range (n + 1)).sum fun i => count i k * i) = m * n by
    rw [← h, Nat.add_sub_cancel]
  simp_rw [← sum_add_distrib, ← mul_add]
  have hn : ∀ x ∈ Finset.range (n + 1), count x ↑k * (n - x + x) = count x ↑k * n := fun _ hx ↦ by
    rw [Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))]
  rw [sum_congr rfl hn, ← sum_mul, range_sym_prop hk]

#find_home sum_range_sym_mul_compl
