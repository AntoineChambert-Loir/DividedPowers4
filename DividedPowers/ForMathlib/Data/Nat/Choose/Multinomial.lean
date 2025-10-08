/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Nat.Choose.Multinomial

/-! # Multinomial

We provide some lemmas for manipulating multinomial coefficients.

-/

section

namespace Nat

open Finset

theorem multinomial_congr_of_sdiff {α : Type*} [DecidableEq α] {f g : α → ℕ} {s t : Finset α}
    (hst : s ⊆ t) (H1 : ∀ a ∈ t \ s, g a = 0) (H2 : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial t g := by
  rw [← Nat.mul_right_inj (a := ∏ a ∈ t, (g a)!), multinomial_spec,
    ← sum_subset_zero_on_sdiff hst H1 H2, ← multinomial_spec s f]
  · apply congr_arg₂ _ _ rfl
    symm
    apply prod_subset_one_on_sdiff hst
    · intro x hx
      rw [H1 x hx, factorial_zero]
    · intro x hx
      rw [H2 x hx]
  · simp only [ne_eq, prod_eq_zero_iff, not_exists, not_and]
    intro x hx
    exact factorial_ne_zero (g x)

theorem multinomial_single {α : Type*} [DecidableEq α] (s : Finset α) (a : α) (n : ℕ) :
    multinomial s (Pi.single a n) = 1 := by
  rw [← Nat.mul_right_inj, mul_one, multinomial_spec]
  · simp only [sum_pi_single']
    split_ifs with ha
    · rw [Finset.prod_eq_single a]
      · simp
      · intro b hb hba
        simp [Pi.single_apply, if_neg hba]
      · simp_all
    · rw [eq_comm, factorial_zero]
      apply Finset.prod_eq_one
      intro b hb
      rw [Pi.single_apply, if_neg, factorial_zero]
      exact ne_of_mem_of_not_mem hb ha
  · simp only [ne_eq, prod_eq_zero_iff, not_exists, not_and]
    intro x hx
    apply factorial_ne_zero

end Nat
