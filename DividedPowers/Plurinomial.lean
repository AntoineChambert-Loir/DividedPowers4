/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.List.ToFinsupp

open List Multiset Nat

lemma List.toFinsupp_support_subset {α : Type*} [Zero α] [DecidableEq α] (l : List α) :
    l.toFinsupp.support ⊆ Finset.range l.length := by
  simp [List.toFinsupp_support]

lemma List.toFinsupp_sum {α : Type*} [AddCommMonoid α] [DecidableEq α] (l : List α) :
    l.toFinsupp.sum (fun _ a ↦ a) = l.sum := by
  match l with
  | nil => simp
  | x :: l =>
    simp only [toFinsupp_cons_eq_single_add_embDomain, sum_cons]
    rw [Finsupp.sum_add_index (by simp) (by simp)]
    simp only [Finsupp.sum_single_index, Finsupp.sum_embDomain, l.toFinsupp_sum]

def List.plurinomial (l : List ℕ) : ℕ :=
  l.toFinsupp.multinomial

theorem List.plurinomial_cons (x : ℕ) (l : List ℕ) :
    (x :: l).plurinomial = Nat.choose (x + l.sum) x * l.plurinomial := by
  simp only [List.plurinomial]
  rw [Finsupp.multinomial_update 0 (x :: l).toFinsupp]
  congr 1
  · congr
    exact List.toFinsupp_sum (x :: l)
  simp only [toFinsupp_cons_eq_single_add_embDomain, Finsupp.multinomial_eq]
  have : (Finsupp.single 0 x + Finsupp.embDomain { toFun := succ, inj' := succ_injective } l.toFinsupp).update 0 0 = (Finsupp.embDomain { toFun := succ, inj' := succ_injective } l.toFinsupp).update 0 0 := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [Finsupp.update_apply, if_neg hi, Finsupp.single_eq_of_ne hi]
  have h (x) : (Finsupp.embDomain { toFun := succ, inj' := succ_injective } l.toFinsupp) (x + 1) = l[x]?.getD 0 := by
    rw [Finsupp.embDomain_apply, dif_pos ⟨x, by simp⟩]
    simp
  simp [this, Nat.multinomial, h]

/-- The `plurinomial` coefficients on `Multiset ℕ`. -/
def Multiset.plurinomial (m : Multiset ℕ) : ℕ := by
  apply Quot.liftOn m (fun l ↦ l.plurinomial)
  intro l l' h
  induction h with
  | nil => simp
  | @cons x l l' hl hl' => simp [List.plurinomial_cons, hl', hl.sum_nat]
  | @swap x y l =>
    simp only [List.plurinomial_cons, ← mul_assoc, List.sum_cons]
    rw [← Nat.choose_symm (Nat.le_add_right y _), add_tsub_cancel_left]
    rw [add_left_comm, Nat.choose_mul (Nat.le_add_right _ _), add_tsub_cancel_left]
    simp [← Nat.choose_symm (Nat.le_add_right _ _), add_tsub_cancel_left]
  | @trans l l' l'' h h' ih ih' => rw [ih, ← ih']

theorem Multiset.plurinomial_cons (x : ℕ) (m : Multiset ℕ) :
    (x ::ₘ m).plurinomial = Nat.choose (x + m.sum) x * m.plurinomial := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact List.plurinomial_cons x l

theorem Multiset.plurinomial_zero : Multiset.plurinomial 0 = 1 := by
  rfl

#eval Multiset.plurinomial {1, 2, 2}
