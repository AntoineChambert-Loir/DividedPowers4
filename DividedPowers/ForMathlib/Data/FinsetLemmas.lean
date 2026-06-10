/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Finset.Sym

/-! # Auxiliary results about `Finset`s -/

section

namespace Finset

open Sym

-- Now Finset.prod_smul in Mathlib
-- theorem prod_smul' {α β ι : Type*} [CommMonoid β] [CommMonoid α] [MulAction α β]
--     [IsScalarTower α β β] [SMulCommClass α β β] (s : Finset ι) (b : ι → α) (f : ι → β) :
--     ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
--   induction s using cons_induction_on with
--   | empty =>  simp
--   | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

/- lemma sym_map {α β : Type*} [DecidableEq α] [DecidableEq β] {n : ℕ} (g : α ↪ β) (s : Finset α) :
    (s.map g).sym n = (s.sym n).map ⟨Sym.map g, Sym.map_injective g.injective _⟩ := by
  ext d
  simp only [mem_sym_iff, mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hd
    let g' : {x // x ∈ d} → α := fun ⟨x, hx⟩ ↦ (hd x hx).choose
    let h : Sym {x // x ∈ d} n → Sym α n := fun p ↦ Sym.map g' p
    use h d.attach
    constructor
    · simp only [Sym.mem_map, Sym.mem_attach, true_and, Subtype.exists, forall_exists_index, h, g']
      intro i e he hi
      rw [← hi]
      exact (hd e he).choose_spec.1
    · simp only [Sym.map_map, Function.comp_apply, h, g']
      convert Sym.attach_map_coe d with ⟨x, hx⟩ hx'
      exact (hd x hx).choose_spec.2
  · rintro ⟨b, hb, rfl⟩ d hd
    simp only [Sym.mem_map] at hd
    obtain ⟨a, ha, rfl⟩ := hd
    refine ⟨a, hb a ha, rfl⟩ -/

end Finset

namespace Sym

open Finset

-- In #40415. Renamed to `Finset.sum_count_sym_eq_val_sum` in the PR (might change).
theorem sum_eq_val_sum {ι : Type*} [DecidableEq ι] {n : ℕ} {k : Sym (ι →₀ ℕ) n}
    {s : Finset (ι →₀ ℕ)} (hk : k ∈ s.sym n) :
    ∑ d ∈ s, Multiset.count d k • d = k.val.sum := by
  induction n with
  | zero =>
    have : k = 0 := Sym.uniqueZero.eq_default k
    simp [this]
  | succ n hrec =>
    simp only [sym_succ, Nat.succ_eq_add_one, mem_sup, mem_image] at hk
    obtain ⟨a, hat, k, hk, rfl⟩ := hk
    simp only [coe_cons, Multiset.count_cons, add_smul, ite_smul, one_smul, zero_nsmul, val_eq_coe,
      Nat.succ_eq_add_one, Multiset.sum_cons, sum_add_distrib]
    nth_rewrite 2 [sum_eq_single a (fun _ _ hab ↦ by rw [if_neg hab]) (fun has ↦ (has hat).elim)]
    rw [if_pos rfl, add_comm, hrec hk, val_eq_coe]

end Sym
