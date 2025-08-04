import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Defs

open Equiv Finsupp Function Set

section Finset

-- Mathlib.Algebra.BigOperators.Group.Finset.Basic
@[to_additive]
theorem Finset.prod_congr_equiv {α β M : Type*} [CommMonoid M] {f : α → M} {s : Finset α}
    (e : α ≃ β) : s.prod f = (s.map e).prod (f ∘ e.symm)  := by
  simp [comp_apply, prod_map, coe_toEmbedding, symm_apply_apply]

-- Mathlib.Algebra.BigOperators.Group.Finset.Basic
@[to_additive]
theorem Finset.prod_congr_equiv' {α β M : Type*} [CommMonoid M] {f : β → M} {s : Finset α}
    (e : α ≃ β) : s.prod (f ∘ e) = (s.map e).prod f := by
  simp [comp_apply, prod_map, coe_toEmbedding]

end Finset

-- Mathlib.Data.Finsupp.Defs
theorem Finsupp.ofSupportFinite_support {ι α : Type*} [Zero α] {f : ι → α} (hf : f.support.Finite) :
    (ofSupportFinite f hf).support = hf.toFinset := by
  ext; simp [ofSupportFinite_coe, mem_support_iff, Finite.mem_toFinset, mem_support]
