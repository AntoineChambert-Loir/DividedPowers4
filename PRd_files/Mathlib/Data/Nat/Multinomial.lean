/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Nat.Choose.Multinomial

/-! # Multinomial

We provide some lemmas for manipulating multinomial coefficients.

-/

-- In #35756

section

namespace Nat

open Finset

theorem multinomial_congr_of_sdiff {α : Type*} [DecidableEq α] {f g : α → ℕ} {s t : Finset α}
    (hst : s ⊆ t) (hf : ∀ a ∈ t \ s, g a = 0) (hg : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial t g := by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun x _ ↦ factorial_ne_zero (g x))),
    multinomial_spec, ← sum_subset_zero_on_sdiff hst hf hg, ← multinomial_spec s f]
  apply congr_arg₂ _ _ rfl
  symm
  apply prod_subset_one_on_sdiff hst
  · intro x hx
    rw [hf x hx, factorial_zero]
  · intro x hx
    rw [hg x hx]

theorem multinomial_single {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (n : ℕ) :
    multinomial s (Pi.single a n) = 1 := by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun _ _ ↦ factorial_ne_zero _)), mul_one,
    multinomial_spec, sum_pi_single']
  split_ifs with ha
  · rw [Finset.prod_eq_single a (by simp_all) (by simp_all), Pi.single_eq_same]
  · rw [eq_comm, factorial_zero]
    apply Finset.prod_eq_one
    intro _ hb
    rw [Pi.single_apply, if_neg (ne_of_mem_of_not_mem hb ha), factorial_zero]

end Nat
