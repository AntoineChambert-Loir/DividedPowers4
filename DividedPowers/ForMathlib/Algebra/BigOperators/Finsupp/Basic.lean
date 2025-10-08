/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open Finset

theorem Finsupp.sum_eq_one_iff {α : Type*} [DecidableEq α] (d : α →₀ ℕ) :
    Finsupp.sum d (fun _ n ↦ n) = 1 ↔ ∃ a, Finsupp.single a 1 = d := by
  refine ⟨fun h1 ↦ ?_, ?_⟩
  · have hd0 : d ≠ 0 := fun h ↦ by simp [h] at h1
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.mp hd0
    rw [Finsupp.coe_zero, Pi.zero_apply, ne_eq] at ha
    rw [← Finsupp.add_sum_erase' _ a, Nat.add_eq_one_iff] at h1
    rcases h1 with (⟨ha', _⟩ | ⟨ha, ha'⟩)
    · exact absurd ha' ha
    · use a
      simp only [Finsupp.sum, Finsupp.support_erase, sum_eq_zero_iff, mem_erase] at ha'
      ext b
      by_cases hb : b = a
      · rw [hb, Finsupp.single_eq_same, ha]
      · rw [Finsupp.single_eq_of_ne hb, eq_comm]
        simp only [Finsupp.mem_support_iff, and_imp] at ha'
        simpa [Finsupp.erase_ne hb] using ha' b (hb)
    · exact fun _ ↦ rfl
  · rintro ⟨a, rfl⟩
    rw [Finsupp.sum_eq_single a ?_ (fun _ ↦ rfl), Finsupp.single_eq_same]
    exact fun _ _ hba ↦ Finsupp.single_eq_of_ne hba
