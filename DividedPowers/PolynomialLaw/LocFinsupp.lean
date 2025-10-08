/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.ForMathlib.Algebra.BigOperators.Group.Finset.Basic
import DividedPowers.PolynomialLaw.Basic

/-! # Locally finite families of polynomial maps and their sums

* `PolynomialLaw.LocFinsupp`:
  A family `f : ι → M →ₚₗ[R] N` of polynomial laws has locally finite support
  if, for all `S`, the function `i ↦ (f i).toFun' S` has finite support`.

* `PolynomialLaw.LocFinsupp.sum`: the sum of a locally finite family of polynomial laws,
  as a polynomial law.

* `PolynomialLaw.lfsum` : the sum of an arbitray family of polynomial laws, extended by `0` when
  it is not locally finite.

-/

namespace PolynomialLaw

universe u

variable {R : Type u} [CommSemiring R] {M N ι : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {f g : ι → M →ₚₗ[R] N}

section LocFinsupp

open Finset TensorProduct

open Finsupp Function

/-- A family `f : ι → M →ₚₗ[R] N` of polynomial laws has locally finite support
  if, for all `S`, the function `i ↦ (f i).toFun' S` has finite support`. -/
def LocFinsupp (f : ι → M →ₚₗ[R] N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M),
    (fun i ↦ (f i).toFun' S m).support.Finite

variable {f g : ι → M →ₚₗ[R] N}

theorem locFinsupp_add (hf : LocFinsupp f) (hg : LocFinsupp g) : LocFinsupp (f + g) :=
  fun S _ _ m ↦ (Set.finite_union.mpr ⟨hf S m, hg S m⟩).subset (support_add _ _)

theorem locFinsupp_zero : LocFinsupp (0 : ι → M →ₚₗ[R] N) :=
  fun S _ _ _ ↦ by simp [zero_def, Set.finite_empty]

theorem locFinsupp_smul (hf : LocFinsupp f) (r : R) :
    LocFinsupp (r • f) := fun S _ _ m ↦ (hf S m).subset (Function.support_smul_subset_right _ _)

variable (f) in
lemma locFinsupp_of_fintype [Fintype ι] : LocFinsupp f := fun _ _ _ _ ↦ Set.toFinite _

variable (R M N) in
/-- The submodule of families of polynomial laws which have locally finite support.  -/
def Submodule.locFinsupp (ι : Type*) : Submodule R (ι → M →ₚₗ[R] N) where
  carrier   := LocFinsupp
  add_mem'  := locFinsupp_add
  zero_mem' := locFinsupp_zero
  smul_mem' r _ hf := locFinsupp_smul hf r

/-- The sum of a locally finite family of polynomial laws. -/
noncomputable def LocFinsupp.sum (hf : LocFinsupp f) :
    M →ₚₗ[R] N where
  toFun'    := fun S _ _ m ↦ (ofSupportFinite _ (hf S m)).sum fun _ m ↦ m
  isCompat' := fun {S _ _ S' _ _} φ ↦ by
    ext m
    simp only [Function.comp_apply, map_finsuppSum]
    rw [Finsupp.sum]
    suffices hSm : _ ⊆ (hf S m).toFinset by
      rw [sum_of_support_subset _ hSm _ (fun i _ ↦ rfl)]
      exact sum_congr rfl (fun i _ ↦ by simp [ofSupportFinite_coe, isCompat_apply'])
    intro i
    simp only [ofSupportFinite_coe, not_imp_not, Finsupp.mem_support_iff,
      Set.Finite.mem_toFinset, Function.mem_support, ← isCompat_apply']
    intro hi
    rw [hi, map_zero]

theorem LocFinsupp.sum_toFun'_eq_finsupp_sum (hf : LocFinsupp f)
    (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    hf.sum.toFun' S m = (ofSupportFinite _ (hf S m)).sum fun _ m ↦ m := rfl

theorem support_ground_finite (hf : LocFinsupp f) (m : M) :
    (Function.support fun i ↦ (f i).ground m).Finite := by
  simp only [ground, Function.comp_apply, lid_symm_apply]
  convert (hf R _ : (Function.support fun i ↦ ((f i).toFun' R (1 ⊗ₜ[R] m))).Finite)
  ext i
  simp only [mem_support, ne_eq, EmbeddingLike.map_eq_zero_iff]

theorem LocFinsupp.sum_ground_eq_finsupp_sum (hf : LocFinsupp f)
    (m : M) :
    hf.sum.ground m =
      (ofSupportFinite (fun i ↦ (f i).ground m) (support_ground_finite hf m)).sum fun _ m ↦ m := by
  simp only [ground, Function.comp_apply, lid_symm_apply]
  rw [hf.sum_toFun'_eq_finsupp_sum, map_finsuppSum, Finsupp.sum, Finsupp.sum]
  congr
  ext i
  simp only [Finsupp.mem_support_iff, ofSupportFinite_coe, ne_eq, EmbeddingLike.map_eq_zero_iff]

theorem LocFinsupp.support_toFun_finite (hf : LocFinsupp f)
    (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (Function.support (fun i ↦ (f i).toFun S m)).Finite := by
  obtain ⟨n, ψ, p, hm⟩ := exists_lift m
  apply Set.Finite.subset (hf _ p)
  intro i
  simp only [mem_support, ne_eq, ← hm, ← isCompat_apply, not_imp_not, toFun_eq_toFun']
  intro hi
  simp [hi]

theorem LocFinsupp.sum_toFun_eq_finsupp_sum (hf : LocFinsupp f)
    (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    hf.sum.toFun S m = (ofSupportFinite (fun i ↦ (f i).toFun S m)
      (hf.support_toFun_finite S m)).sum fun _ m ↦ m := by
  obtain ⟨n, ψ, p, hm⟩ := exists_lift m
  rw [← hm, ← isCompat_apply, toFun_eq_toFun', hf.sum_toFun'_eq_finsupp_sum, map_finsuppSum]
  simp_rw [← isCompat_apply, toFun_eq_toFun']
  rw [Finsupp.sum, Finsupp.sum_of_support_subset]
  · apply Finset.sum_congr rfl
    simp [Finsupp.ofSupportFinite_coe]
  · intro i
    simp only [mem_support_iff, ne_eq, not_imp_not, Finsupp.ofSupportFinite_coe]
    intro hi
    simp [hi]
  · simp

/-- The sum of a locally finite family of polynomial laws, as a linear map. -/
noncomputable def lfsumHom : Submodule.locFinsupp R M N ι →ₗ[R] M →ₚₗ[R] N where
  toFun fhf := LocFinsupp.sum fhf.prop
  map_add'  := fun ⟨f, hf⟩ ⟨g, hg⟩ ↦ by
    classical
    ext S _ _ m
    simp only [LocFinsupp.sum, AddMemClass.mk_add_mk, Pi.add_apply, add_def]
    rw [sum_of_support_subset (s := (hf S m).toFinset ∪ (hg S m).toFinset) _ _ _ (fun _ _ ↦ rfl),
      sum_of_support_subset _ subset_union_left _ (fun _ _ ↦ rfl),
      sum_of_support_subset _ subset_union_right _ (fun _ _ ↦ rfl), ← sum_add_distrib]
    · exact sum_congr rfl (fun _ _ ↦ rfl)
    · intro x
      simp only [ofSupportFinite_support, Set.Finite.mem_toFinset,
        Function.mem_support, ne_eq, mem_union, ← not_and_or, not_imp_not]
      intro h
      rw [h.1, h.2, add_zero]
  map_smul' := fun a ⟨f,hf⟩ ↦ by
    ext S _ _ m
    simp only [LocFinsupp.sum, SetLike.mk_smul_mk, Pi.smul_apply, smul_def, RingHom.id_apply]
    rw [sum_of_support_subset _ _ _ (fun i _ ↦ rfl)]
    · rw [Finsupp.smul_sum, sum]
      exact sum_congr rfl fun i _ ↦ rfl
    · intro i
      simp only [ofSupportFinite_coe, Finsupp.mem_support_iff, ne_eq, not_imp_not]
      intro hi
      rw [hi, smul_zero]

variable (f)

open Classical in
/-- The sum of of a family of polynomial laws (0 if not locally finite). -/
noncomputable def lfsum : M →ₚₗ[R] N :=
  if hf : LocFinsupp f then hf.sum else 0

variable {f}

theorem lfsum_toFun'_eq_of_locFinsupp (hf : LocFinsupp f)
    (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (lfsum f).toFun' S m = (ofSupportFinite _ (hf S m)).sum fun _ m ↦ m := by
  rw [lfsum, dif_pos hf, hf.sum_toFun'_eq_finsupp_sum]

lemma lfsumHom_apply' {f : ↥(Submodule.locFinsupp R M N ι)} : lfsumHom f = lfsum f.val := by
  simp only [lfsumHom, LinearMap.coe_mk, AddHom.coe_mk, lfsum]
  rw [dif_pos (by exact f.prop)]

lemma lfsumHom_apply (hf : LocFinsupp f) :
    lfsumHom ⟨f, hf⟩ = lfsum f := by
  simp only [lfsumHom, LinearMap.coe_mk, AddHom.coe_mk, lfsum, dif_pos hf]

lemma lfsumHom_add (hf : LocFinsupp f) (hg : LocFinsupp g) (hfg : LocFinsupp (f + g)) :
    lfsumHom ⟨(f + g), hfg⟩ = lfsumHom ⟨f, hf⟩ + lfsumHom ⟨g, hg⟩ := by
  rw [← map_add, AddMemClass.add_def]

lemma lfsumHom_smul (hf : LocFinsupp f) {r : R} (hrf : LocFinsupp (r • f)) :
    lfsumHom ⟨r • f, hrf⟩ = r • lfsumHom ⟨f, hf⟩ := by
  rw [← map_smul, SetLike.smul_of_tower_def]

theorem lfsum_ground_eq_of_locFinsupp (hf : LocFinsupp f) (m : M) :
    (lfsum f).ground m =
      (ofSupportFinite (fun i ↦ (f i).ground m) (support_ground_finite hf m)).sum fun _ m ↦ m := by
  simp only [ground, Function.comp_apply, lid_symm_apply]
  rw [lfsum_toFun'_eq_of_locFinsupp hf]
  rw [map_finsuppSum, Finsupp.sum, Finsupp.sum]
  congr
  ext i
  simp only [Finsupp.mem_support_iff, ofSupportFinite_coe, ne_eq, EmbeddingLike.map_eq_zero_iff]

end LocFinsupp
