/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowers.BasicLemmas
import DividedPowers.Exponential
--import DividedPowers.ForMathlib.LinearAlgebra.OnSup
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.RingTheory.DividedPowers.RatAlgebra
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.Data.Nat.Choose.Vandermonde

/-! # Divided powers on sums of ideals
Let `A` be a commutative ring and let `(I, hI)` and `(J, hJ)` be two divided power ideals in `A`
such that `hI` and `hJ` agree on the intersection `hI ∩ hJ`. In this file, we construct the unique
divided power structure on `I + J` that extends both `hI` and `hJ`.

## Main definitions
* `DividedPowers.IdealAdd.dividedPowers`: the divided power structure on the ideal `I + J`, given
  that `hI` and `hJ` agree on `I ⊓ J`.
* `DividedPowers.IdealAdd.subDPIdeal_left`: `I` as a `SubDPIdeal` of `I + J`.
* `DividedPowers.IdealAdd.subDPIdeal_right`: `J` as a `SubDPIdeal` of `I + J`.

## Main results
* `DividedPowers.IdealAdd.dividedPowers_unique`: `IdealAdd.dividedPowers` is the unique divided
  power structure on `I + J` that simultaneously extends `hI` and `hJ`.
* `DividedPowers.IdealAdd.isDPMorphism_left`: `id A` is a `DPMorphism` from `I` to `I + J`.
* `DividedPowers.IdealAdd.isDPMorphism_right`: `id A` is a `DPMorphism` from `J` to `I + J`.

## References
* [P. Berthelot, *Cohomologie cristalline des schémas de
caractéristique $p$ > 0*][Berthelot-1974]
* [P. Berthelot and A. Ogus, *Notes on crystalline
cohomology*][BerthelotOgus-1978]
* [N. Roby, *Lois polynomes et lois formelles en théorie des
modules*][Roby-1963]
* [N. Roby, *Les algèbres à puissances dividées*][Roby-1965]

## Implementation Remarks
See the file `IdealAdd_v1.lean` for a mathematically equivalent definition of the divided power
structure on `I + J` that does not rely on exponential power series.
-/

namespace DividedPowers

open Nat PowerSeries

/- We need `A` to be a ring, until `ExponentialModule` is generalized to `CommSemiring`. -/

variable {A : Type*} [CommRing A] {I J : Ideal A} {hI : DividedPowers I} {hJ : DividedPowers J}

-- TODO: PR the next two lemmas to `Mathlib.RingTheory.DividedPowers.Basic`.
theorem coeff_exp (n : ℕ) (a : A) : coeff n (hI.exp a) = hI.dpow n a := by
  simp only [exp, coeff_mk]

theorem constantCoeff_exp {a : A} (ha : a ∈ I) : constantCoeff (hI.exp a) = 1 := by
  simp only [exp, constantCoeff_mk, hI.dpow_zero ha]

namespace IdealAdd

open Finset BigOperators Polynomial

/-- Some complicated numerical coefficients for the proof of `IdealAdd.dpow_comp`. -/
private def cnik (n i : ℕ) (k : Multiset ℕ) : ℕ :=
  if i = 0 then (k.count i).uniformBell n
    else if i = n then  (k.count i).uniformBell n
      else (k.count i).factorial * (k.count i).uniformBell i * (k.count i).uniformBell (n - i)

/-- The exponential map on the sup of two compatible divided power ideals. -/
noncomputable def exp'_linearMap (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    (I + J) →ₗ.[A] (ExponentialModule A) := by
  set f : (I + J) →ₗ.[A] (ExponentialModule A) := {
    domain := {
      carrier := {x : I + J | (x : A) ∈ I}
      add_mem' hx hy := by
        simp only [Submodule.add_eq_sup, Set.mem_setOf_eq, Submodule.coe_add] at hx hy ⊢
        exact (Submodule.add_mem_iff_right I hx).mpr hy
      zero_mem' := by simp
      smul_mem' a x hx := by
        simp only [Submodule.add_eq_sup, Set.mem_setOf_eq, SetLike.val_smul, smul_eq_mul] at hx ⊢
        exact Ideal.mul_mem_left I a hx}
    toFun := {
      toFun x := hI.exp'_linearMap ⟨(x : A), x.2⟩
      map_add' := sorry
      map_smul' := sorry
    }
  } with hf_def
  set g : (I + J) →ₗ.[A] (ExponentialModule A) := {
    domain := {
      carrier := {x : I + J | (x : A) ∈ J}
      add_mem' hx hy := by
        simp only [Submodule.add_eq_sup, Set.mem_setOf_eq, Submodule.coe_add] at hx hy ⊢
        exact (Submodule.add_mem_iff_right J hx).mpr hy
      zero_mem' := by simp
      smul_mem' a x hx := by
        simp only [Submodule.add_eq_sup, Set.mem_setOf_eq, SetLike.val_smul, smul_eq_mul] at hx ⊢
        exact Ideal.mul_mem_left J a hx }
    toFun := {
      toFun x := hJ.exp'_linearMap ⟨(x : A), x.2⟩
      map_add' := sorry
      map_smul' := sorry
    }
  } with hg_def
  have hf : (f.domain : Set (I + J)) =  {x : I + J | (x : A) ∈ I} := rfl
  have hg : (g.domain : Set (I + J)) =  {x : I + J | (x : A) ∈ J} := rfl
  apply LinearPMap.sup f g
  intro x y hxy
  have hx := x.2
  have hy := y.2
  erw [Submodule.mem_carrier, hf, Set.mem_setOf_eq] at hx
  erw [Submodule.mem_carrier, hg,  Set.mem_setOf_eq, ← hxy] at hy
  apply Subtype.coe_inj.mp (Additive.toMul.injective (PowerSeries.ext ?_ ))
  intro n
  convert hIJ x ⟨hx, hy⟩
  sorry

  /- LinearMap.onSup (f := hI.exp'_linearMap) (g := hJ.exp'_linearMap)
    (fun x hxI hxJ ↦ Subtype.coe_inj.mp
      (Additive.toMul.injective (PowerSeries.ext (fun _ ↦ hIJ x ⟨hxI, hxJ⟩)))) -/

#exit

theorem exp'_linearMap_apply (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {x y : A} (hx : x ∈ I) (hy : y ∈ J) :
    exp'_linearMap hIJ ⟨x + y, Submodule.add_mem_sup hx hy⟩ =
      hI.exp'_linearMap ⟨x, hx⟩ + hJ.exp'_linearMap ⟨y, hy⟩ := by
  rw [exp'_linearMap, LinearMap.onSup_apply]

theorem exp'_linearMap_apply_left (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {x : A}
    (hx : x ∈ I) : exp'_linearMap hIJ ⟨x, Ideal.mem_sup_left hx⟩ = hI.exp'_linearMap ⟨x, hx⟩ := by
  rw [exp'_linearMap, LinearMap.onSup_apply_left _ hx]

theorem exp'_linearMap_apply_right (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {y : A} (hy : y ∈ J) :
    exp'_linearMap hIJ ⟨y, Ideal.mem_sup_right hy⟩ = hJ.exp'_linearMap ⟨y, hy⟩ := by
  rw [exp'_linearMap, LinearMap.onSup_apply_right _ hy]

/-- The divided power function on the sup of two ideals `I` and `J` extending divided power
  structures `hI` and `hJ` that agree on `I ∩ J`. -/
noncomputable def dpow (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) :=
  Function.extend (fun a ↦ ↑a : (I + J) → A) (fun a ↦ coeff n (exp'_linearMap hIJ a)) (0 :  A → A)

theorem dpow_def (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) (n : ℕ) {a : A}
    (ha : a ∈ I + J) : dpow hIJ n a = coeff n (exp'_linearMap hIJ ⟨a, ha⟩) :=
  Subtype.val_injective.extend_apply _ _ ⟨a, ha⟩

theorem dpow_eq (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {a b : A} (ha : a ∈ I) (hb : b ∈ J) :
    dpow hIJ n (a + b) = ∑ k ∈ (antidiagonal n), hI.dpow k.1 a * hJ.dpow k.2 b := by
  rw [dpow_def, exp'_linearMap_apply hIJ ha hb, ExponentialModule.coe_add, PowerSeries.coeff_mul]
  apply congr_arg₂ _ rfl
  ext ⟨u, v⟩
  simp only [DividedPowers.exp'_linearMap_apply, coeff_exp]

lemma _root_.antidiagonal_eq_filter {A : Type*} [AddCommMonoid A] [PartialOrder A]
    [IsOrderedAddMonoid A] [CanonicallyOrderedAdd A] [LocallyFiniteOrderBot A] [DecidableEq A]
    [HasAntidiagonal A] (n : A) :
    antidiagonal n = (Iic n ×ˢ Iic n).filter (fun x : A × A ↦ x.1 + x.2 = n) := by
  ext ⟨i, j⟩
  simp only [mem_antidiagonal, mem_filter, mem_product, mem_Iic, iff_and_self]
  rintro rfl
  simp

nonrec lemma _root_.Nat.antidiagonal_eq_filter (n : ℕ) :
    antidiagonal n = (Icc 0 n ×ˢ Icc 0 n).filter (fun x : ℕ × ℕ ↦ x.1 + x.2 = n) := by
  rw [antidiagonal_eq_filter, Iic_eq_Icc, bot_eq_zero]

theorem dpow_eq' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {a b : A} (ha : a ∈ I) (hb : b ∈ J) :
    dpow hIJ n (a + b) =
      ∑ k ∈ Icc 0 n, ∑ l ∈ Icc 0 n, if k + l = n then hI.dpow k a * hJ.dpow l b else 0 := by
  rw [dpow_eq hIJ ha hb, antidiagonal_eq_filter, sum_filter, sum_product]

private theorem dpow_eq_of_mem_left' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ I) :
    dpow hIJ n x = hI.dpow n x := by
  rw [dpow_def, exp'_linearMap_apply_left hIJ hx]
  simp only [DividedPowers.exp'_linearMap_apply, coeff_exp]

private theorem dpow_eq_of_mem_right' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ J) :
    dpow hIJ n x = hJ.dpow n x := by
  rw [dpow_def, exp'_linearMap_apply_right hIJ hx]
  simp only [DividedPowers.exp'_linearMap_apply, coeff_exp]

theorem dpow_zero (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {x : A} (hx : x ∈ I + J) : dpow hIJ 0 x = 1 := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp [dpow_eq hIJ ha hb, antidiagonal_zero, Prod.mk_zero_zero, sum_singleton, Prod.fst_zero,
    Prod.snd_zero, hI.dpow_zero ha, hJ.dpow_zero hb, mul_one]

theorem mul_dpow (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {m n : ℕ} {x : A} (hx : x ∈ I + J) :
    dpow hIJ m x * dpow hIJ n x = ((m + n).choose m) * dpow hIJ (m + n) x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp only [dpow_eq hIJ ha hb, sum_mul_sum, ← sum_product']
  have hf : ∀ x : (ℕ × ℕ) × ℕ × ℕ,
      hI.dpow x.1.1 a * hJ.dpow x.1.2 b * (hI.dpow x.2.1 a * hJ.dpow x.2.2 b) =
        (x.1.1 + x.2.1).choose x.1.1 * (x.1.2 + x.2.2).choose x.1.2 *
            hI.dpow (x.1.1 + x.2.1) a * hJ.dpow (x.1.2 + x.2.2) b := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
    rw [mul_assoc, ← mul_assoc (hJ.dpow j b), mul_comm (hJ.dpow j b), mul_assoc, hJ.mul_dpow hb,
      ← mul_assoc, hI.mul_dpow ha]
    ring
  rw [sum_congr rfl fun x _ ↦ hf x]
  set s : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := fun x ↦ ⟨x.1.1 + x.2.1, x.1.2 + x.2.2⟩ with hs_def
  have hs : ∀ x ∈ antidiagonal m ×ˢ antidiagonal n, s x ∈ antidiagonal (m + n) := by
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ h
    simp only [mem_antidiagonal, mem_product] at h ⊢
    rw [add_assoc, ← add_assoc k j l, add_comm k _, add_assoc, h.2, ← add_assoc, h.1]
  rw [← sum_fiberwise_of_maps_to hs]
  have hs' : ∑ y ∈ antidiagonal (m + n),
      ∑ x ∈ ((antidiagonal m ×ˢ antidiagonal n).filter (fun x ↦ s x = y)),
          ((x.1.1 + x.2.1).choose x.1.1) * ((x.1.2 + x.2.2).choose x.1.2) *
            hI.dpow (x.1.1 + x.2.1) a * hJ.dpow (x.1.2 + x.2.2) b =
      ∑ y ∈ antidiagonal (m + n),
        (∑ x ∈ ((antidiagonal m ×ˢ antidiagonal n).filter (fun x ↦ s x = y)),
          ((y.fst.choose x.1.1) * (y.snd.choose x.1.2))) * hI.dpow y.fst a * hJ.dpow y.snd b := by
    apply sum_congr rfl
    rintro ⟨u, v⟩ _
    simp only [cast_sum, cast_mul, sum_mul]
    apply sum_congr rfl
    rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ hx
    simp only [hs_def, mem_product, mem_antidiagonal, mem_filter, Prod.mk.injEq] at hx
    rw [hx.2.1, hx.2.2]
  rw [hs', mul_sum]
  apply sum_congr rfl
  rintro ⟨u, v⟩ h
  simp only [mem_antidiagonal] at h
  rw [← mul_assoc]
  congr
  simp only [hs_def, Prod.mk.injEq]
  rw [Finset.sum_filter, Finset.sum_product, ← h, add_choose_eq]
  apply Finset.sum_congr rfl
  intro x hx
  -- x1 + x2 = m, y1 + y2 = n, x1 + y1 = u,  x2 + y2 = v
  -- y1 = u - x1, y2 = v - x2
  rw [Finset.sum_eq_single (u-x.1, v - x.2)]
  · simp only [ite_eq_left_iff, not_and_or, zero_eq_mul]
    apply Or.imp
    all_goals {
      rw [choose_eq_zero_iff, ← not_le, not_imp_not]
      exact add_sub_of_le }
  · intro y _ hy'
    simp only [ite_eq_right_iff] --TODO: simp? + golf proof
    intro hy''
    apply False.elim (hy' _)
    ext
    · rw [← Nat.add_right_inj (n := x.1), hy''.1, add_sub_of_le (hy''.1.symm ▸ le_add_right _ _)]
    · rw [← Nat.add_right_inj (n := x.2), hy''.2, add_sub_of_le (hy''.2.symm ▸ le_add_right _ _)]
  · intro hx'
    simp only [ite_eq_right_iff] --TODO: simp? + golf proof
    intro hx''
    apply False.elim (hx' _)
    simp only [mem_antidiagonal] at hx ⊢
    rw [← Nat.add_right_inj (n := x.1), ← add_assoc, hx''.1, ← Nat.add_left_inj (n := x.2),
      add_assoc, add_comm _ x.2, hx''.2, h, add_assoc, add_comm n, ← add_assoc, hx]

theorem dpow_mem (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∈ I + J) : dpow hIJ n x ∈ I + J := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hIJ ha hb]
  refine Submodule.sum_mem (I ⊔ J) (fun k hk ↦ ?_)
  simp only [mem_antidiagonal] at hk
  by_cases h : k.1 = 0
  · simp only [h, zero_add] at hk
    exact hk ▸ Submodule.mem_sup_right (J.mul_mem_left _ (hJ.dpow_mem hn hb))
  · exact Submodule.mem_sup_left (I.mul_mem_right _ (hI.dpow_mem h ha))

theorem dpow_mul (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {c x : A} (hx : x ∈ I + J) : dpow hIJ n (c * x) = c ^ n * dpow hIJ n x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp_rw [dpow_eq hIJ ha hb]
  simp_rw [mul_add c a b]
  rw [dpow_eq hIJ (I.mul_mem_left c ha) (J.mul_mem_left c hb), mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [mem_antidiagonal] at hk
  rw [hI.dpow_mul ha, hJ.dpow_mul hb, mul_mul_mul_comm, ← pow_add, hk]

lemma sum_sum_antidiagonal {β : Type*} [AddCommMonoid β] (f : ℕ → ℕ × ℕ → β) {n : ℕ} :
    ∑ p ∈ Icc 0 n, ∑ k ∈ antidiagonal p, f p k =
      ∑ i ∈ Icc 0 n, ∑ j ∈ Icc 0 n, if i + j ≤ n then f (i + j) (i, j) else 0 := by calc
  _ = ∑ p ∈ Icc 0 n, ∑ a ∈ Icc 0 p ×ˢ Icc 0 p, if a.1 + a.2 = p then f p a else 0 := by
      simp_rw [antidiagonal_eq_filter, sum_filter]
  _ = ∑ p ∈ Icc 0 n, ∑ a ∈ Icc 0 n ×ˢ Icc 0 n, if a.1 + a.2 = p then f p a else 0 := by
      refine sum_congr rfl fun p hp ↦ ?_
      simp only [mem_Icc, _root_.zero_le, true_and] at hp
      exact sum_subset (by gcongr) (by simp; omega)
  _ = ∑ i ∈ Icc 0 n, ∑ j ∈ Icc 0 n, if i + j ≤ n then f (i + j) (i, j) else 0 := by
      simp_rw [sum_product]
      rw [sum_comm]
      refine sum_congr rfl fun i hi ↦ ?_
      rw [sum_comm]
      refine sum_congr rfl fun j hj ↦ ?_
      simp [sum_ite_eq]

theorem dpow_add (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x y : A} (hx : x ∈ I + J) (hy : y ∈ I + J) :
    dpow hIJ n (x + y) = ∑ k ∈ antidiagonal n, dpow hIJ k.1 x * dpow hIJ k.2 y := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨a', ha', b', hb', rfl⟩ := hy
  rw [add_add_add_comm a b a' b', dpow_eq' hIJ (I.add_mem ha ha') (J.add_mem hb hb')]
  calc
    _ = ∑ p ∈ Icc 0 n, ∑ q ∈ Icc 0 n, ∑ l ∈ Icc 0 n, if p + q + l = n
        then hI.dpow p a * hI.dpow q a' * hJ.dpow l (b + b') else 0 := by
      simp_rw [hI.dpow_add ha ha', sum_mul, ite_sum_zero, sum_comm (t := antidiagonal _),
        sum_sum_antidiagonal, ite_sum_zero, ← ite_and]
      congr! 4
      omega
    _ = ∑ p ∈ Icc 0 n, ∑ q ∈ Icc 0 n, ∑ r ∈ Icc 0 n, ∑ s ∈ Icc 0 n, if p + q + (r + s) = n
        then hI.dpow p a * hI.dpow q a' * (hJ.dpow r b * hJ.dpow s b') else 0 := by
      simp_rw [hJ.dpow_add hb hb', mul_sum, ite_sum_zero, sum_sum_antidiagonal, ← ite_and]
      congr! 5
      omega
    _ = ∑ p ∈ Icc 0 n, ∑ q ∈ Icc 0 n, ∑ r ∈ Icc 0 n, ∑ s ∈ Icc 0 n, if p + q + (r + s) = n
        then hI.dpow p a * hJ.dpow q b * (hI.dpow r a' * hJ.dpow s b') else 0 := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [sum_comm]
      congr! 4 with q hq r hq s hs
      · omega
      · ring
    _ = ∑ p ∈ Icc 0 n, ∑ q ∈ Icc 0 n, ∑ l ∈ Icc 0 n, if p + q + l = n
        then hI.dpow p a * hJ.dpow q b * dpow hIJ l (a' + b') else 0 := by
      simp_rw [dpow_eq hIJ ha' hb', mul_sum, ite_sum_zero, sum_sum_antidiagonal, ← ite_and]
      congr! 5
      omega
    _ = ∑ k ∈ antidiagonal n, dpow hIJ k.1 (a + b) * dpow hIJ k.2 (a' + b') := by
      simp_rw [antidiagonal_eq_filter, sum_filter, sum_product, dpow_eq hIJ ha hb, sum_mul,
        ite_sum_zero, sum_comm (t := antidiagonal _), sum_sum_antidiagonal, ite_sum_zero, ← ite_and]
      congr! 4
      omega

theorem dpow_add' (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x y : A} (hx : x ∈ I + J) (hy : y ∈ I + J) :
    dpow hIJ n (x + y) = ∑ k ∈ range (n + 1), dpow hIJ k x * dpow hIJ (n - k) y := by
  simp [dpow_add hIJ hx hy, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The `dpow_comp` axiom for elements of the ideal `I ⊔ J` of the form `a + b` with `a ∈ I` and
  `b ∈ J`. -/
private theorem dpow_comp_aux (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {m n : ℕ}
    (hn : n ≠ 0) {a b : A} (ha : a ∈ I) (hb : b ∈ J) :
    dpow hIJ m (dpow hIJ n (a + b)) = ∑ p ∈ range (m * n + 1),
        (∑ x ∈ ((range (n + 1)).sym m).filter
          (fun l : Sym ℕ m ↦ ∑ i ∈ range (n + 1), Multiset.count i ↑l * i = p),
          ((∏ i ∈ range (n + 1), cnik n i ↑x) *
            multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * i) *
            multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * (n - i)) *
          hI.dpow p a * hJ.dpow (m * n - p) b := by
  rw [dpow_eq hIJ ha hb, Nat.sum_antidiagonal_eq_sum_range_succ
    (f := fun k l ↦ hI.dpow k a * hJ.dpow l b)]
  have L1 (k : Sym ℕ m) (i : ℕ) (hi : i ∈ range (n + 1)) :
      dpow hIJ (Multiset.count i ↑k) (hI.dpow i a * hJ.dpow (n - i) b) = cnik n i ↑k *
        hI.dpow (Multiset.count i ↑k * i) a * hJ.dpow (Multiset.count i ↑k * (n - i)) b := by
    simp only [cnik]
    by_cases hi2 : i = n
    · rw [hi2, Nat.sub_self, if_neg hn, if_pos rfl]
      simp only [hJ.dpow_zero hb, mul_one, mul_zero]
      rw [dpow_eq_of_mem_left' hIJ (hI.dpow_mem hn ha), hI.dpow_comp hn ha]
    · have hi2' : n - i ≠ 0 := by
        intro h; apply hi2
        rw [mem_range, Nat.lt_succ_iff] at hi
        rw [← Nat.sub_add_cancel hi, h, zero_add]
      by_cases hi1 : i = 0
      · rw [hi1, hI.dpow_zero ha, Nat.sub_zero, one_mul, if_pos rfl,
          dpow_eq_of_mem_right' hIJ (hJ.dpow_mem hn hb), hJ.dpow_comp hn hb, mul_zero,
          hI.dpow_zero ha, mul_one]
      -- i ≠ 0  and i ≠ n
      · rw [if_neg hi1, if_neg hi2, mul_comm, dpow_mul hIJ
          (Submodule.mem_sup_left (hI.dpow_mem hi1 ha)), mul_comm, dpow_eq_of_mem_left' hIJ
          (hI.dpow_mem hi1 ha), ← hJ.factorial_mul_dpow_eq_pow (hJ.dpow_mem hi2' hb),
          hI.dpow_comp hi1 ha, hJ.dpow_comp hi2' hb]
        simp only [← mul_assoc]
        apply congr_arg₂ _ _ rfl
        simp only [mul_assoc]
        rw [mul_comm (hI.dpow _ a)]
        simp only [← mul_assoc]
        apply congr_arg₂ _ _ rfl
        simp only [cast_mul]
        apply congr_arg₂ _ _ rfl
        rw [mul_comm]
  rw [dpow_sum' (dpow := dpow hIJ)]
  · set φ := fun (k : Sym ℕ m) ↦ ∑ i ∈ (range (n + 1)), Multiset.count i ↑k * i with hφ_def
    suffices hφ : ∀ k ∈ (range (n + 1)).sym m, φ k ∈ range (m * n + 1) by
      rw [← sum_fiberwise_of_maps_to hφ _]
      suffices L4 : ∀ (p : ℕ) (_ : p ∈ range (m * n + 1)),
          (∑ x ∈ (filter (fun x ↦ φ x = p) ((range (n + 1)).sym m)),
              ∏ i ∈ (range (n + 1)),
                dpow hIJ (Multiset.count i ↑x) (hI.dpow i a * hJ.dpow (n - i) b)) =
            ∑ k ∈ ((range (n + 1)).sym m).filter (fun x ↦ φ x = p),
              (∏ i ∈ (range (n + 1)), ↑(cnik n i ↑k)) *
                  ↑(multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑k * i) *
                  ↑(multinomial (range (n + 1)) fun i : ℕ => Multiset.count i ↑k * (n - i)) *
              hI.dpow p a * hJ.dpow (m * n - p) b by
          simp only [succ_eq_add_one, sum_congr rfl L4, cast_sum, cast_mul, cast_prod, sum_mul]
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
    exact dpow_zero hIJ hx
  . -- dpow_add
    intro n x y
    exact dpow_add hIJ
  · -- dpow_eval_zero
    intro n hn
    rw [dpow_eq_of_mem_left' hIJ I.zero_mem, dpow_eval_zero hI hn]
  · intro i _
    by_cases hi0 : i = 0
    · apply Submodule.mem_sup_right (J.mul_mem_left _ (hJ.dpow_mem ?_ hb))
      rw [hi0, tsub_zero]; exact hn
    · exact Submodule.mem_sup_left (I.mul_mem_right _ (hI.dpow_mem hi0 ha))

private theorem dpow_comp_coeffs {m n p : ℕ} (hn : n ≠ 0) (hp : p ≤ m * n) :
    uniformBell m n = ∑ x ∈ ((range (n + 1)).sym m).filter
      (fun l : Sym ℕ m ↦ ∑ i ∈ range (n + 1), Multiset.count i ↑l * i = p),
        (∏ i ∈ (range (n + 1)), cnik n i ↑x) *
          ((multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * i) *
            multinomial (range (n + 1)) fun i ↦ Multiset.count i ↑x * (n - i)) := by
  classical
  rw [← mul_left_inj' (pos_iff_ne_zero.mp (choose_pos hp))]
  apply @cast_injective ℚ
  simp only [cast_sum, cast_mul, cast_prod]
  conv_lhs => rw [← Polynomial.coeff_X_add_one_pow ℚ (m * n) p]
  let A := ℚ[X]
  let I : Ideal A := ⊤
  let hI : DividedPowers I := RatAlgebra.dividedPowers ⊤
  let hII : ∀ {n : ℕ}, ∀ a ∈ I ⊓ I, hI.dpow n a = hI.dpow n a := fun _ _ => rfl
  let h1 : (1 : A) ∈ I := Submodule.mem_top
  let hX : Polynomial.X ∈ I := Submodule.mem_top
  rw [← hI.factorial_mul_dpow_eq_pow Submodule.mem_top, ← Polynomial.coeff_C_mul,
    ← mul_assoc, mul_comm (Polynomial.C (uniformBell m n : ℚ)), mul_assoc, C_eq_natCast,
    ← hI.dpow_comp hn Submodule.mem_top, ← dpow_eq_of_mem_left' hII Submodule.mem_top,
    ← dpow_eq_of_mem_left' hII Submodule.mem_top, dpow_comp_aux hII hn hX h1,
    ← C_eq_natCast, mul_sum, finset_sum_coeff]
  simp only [hI, RatAlgebra.dpow_eq_inv_fact_smul _ _ Submodule.mem_top, map_natCast,
    Ring.inverse_eq_inv', Algebra.mul_smul_comm, one_pow,
    mul_one, Polynomial.coeff_smul, coeff_natCast_mul, smul_eq_mul]
  simp only [← cast_prod, ← cast_mul, ← cast_sum]
  rw [sum_eq_single p]
  · conv_lhs =>
      rw [coeff_natCast_mul, Polynomial.coeff_X_pow, if_pos, mul_one, ← mul_assoc, mul_comm]
      simp only [mul_assoc]
      rw [mul_comm]
    simp only [cast_sum, cast_mul, cast_prod, sum_mul]
    apply sum_congr rfl
    intro x _
    simp only [mul_assoc]
    congr
    ring_nf
    simp only [mul_assoc]
    rw [inv_mul_eq_iff_eq_mul₀, inv_mul_eq_iff_eq_mul₀, ← choose_mul_factorial_mul_factorial hp]
    simp only [cast_mul]
    ring
    all_goals
      simp only [ne_eq, cast_eq_zero]
      exact factorial_ne_zero _
  · intro b _ hb
    rw [coeff_natCast_mul, Polynomial.coeff_X_pow, if_neg hb.symm]
    simp only [mul_zero]
  · intro hp'
    simp only [mem_range, Nat.lt_succ_iff] at hp'
    contradiction

theorem dpow_comp (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {m n : ℕ} {x : A}
    (hn : n ≠ 0) (hx : x ∈ I + J) :
    dpow hIJ m (dpow hIJ n x) = ↑(uniformBell m n) * dpow hIJ (m * n) x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_comp_aux hIJ hn ha hb,
    dpow_add' hIJ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), mul_sum]
  apply sum_congr rfl
  intro p hp
  rw [dpow_eq_of_mem_left' hIJ ha, dpow_eq_of_mem_right' hIJ hb]
  simp only [mul_assoc]
  apply congr_arg₂ (· * ·) _ rfl
  -- it remains to check coefficients
  rw [dpow_comp_coeffs hn (Nat.lt_succ_iff.mp (mem_range.mp hp))]

theorem dpow_null (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∉ I + J) :
    dpow hIJ n x = 0 := by
  simp only [dpow]
  rw [Function.extend_apply', Pi.zero_apply]
  rintro ⟨a, rfl⟩
  exact hx a.prop

theorem dpow_one (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) {x : A}
   (hx : x ∈ I + J) : dpow hIJ 1 x = x := by
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [dpow_eq hIJ ha hb]
  have h1 : antidiagonal 1 = {⟨0, 1⟩, ⟨1, 0⟩} := rfl
  simp [h1, hI.dpow_one ha, hJ.dpow_one hb, hI.dpow_zero ha, hJ.dpow_zero hb, add_comm]

/-- The divided power structure on the ideal `I + J`, given that `hI` and `hJ` agree on `I ⊓ J`. -/
noncomputable def dividedPowers (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    DividedPowers (I + J) where
  dpow           := dpow hIJ
  dpow_null      := dpow_null hIJ
  dpow_zero      := dpow_zero hIJ
  dpow_one       := dpow_one hIJ
  dpow_mem hn hx := dpow_mem hIJ hn hx
  dpow_add       := dpow_add hIJ
  dpow_mul       := dpow_mul hIJ
  mul_dpow       := mul_dpow hIJ
  dpow_comp      := dpow_comp hIJ

theorem dividedPowers_unique (hsup : DividedPowers (I + J))
    (hI' : ∀ {n : ℕ}, ∀ a ∈ I, hI.dpow n a = hsup.dpow n a)
    (hJ' : ∀ {n : ℕ}, ∀ b ∈ J, hJ.dpow n b = hsup.dpow n b) :
    let hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a := fun n ha => by
      rw [hI' _ ha.1, hJ' _ ha.2]
    hsup = dividedPowers hIJ := by
  intro hIJ
  refine hsup.ext _ (fun n x hx ↦ ?_)
  rw [Ideal.add_eq_sup, Submodule.mem_sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  simp only [hsup.dpow_add (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb),
    IdealAdd.dividedPowers, dpow_eq hIJ ha hb]
  exact sum_congr rfl (fun k _ ↦ congr_arg₂ (· * ·) (hI' a ha).symm (hJ' b hb).symm)

lemma isDPMorphism_left (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    hI.IsDPMorphism (IdealAdd.dividedPowers hIJ) (RingHom.id A):=
  ⟨by simp only [Ideal.map_id]; exact le_sup_left, fun _ ↦ dpow_eq_of_mem_left' hIJ⟩

lemma isDPMorphism_right (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a) :
    hJ.IsDPMorphism (IdealAdd.dividedPowers hIJ) (RingHom.id A) :=
  ⟨by simp only [Ideal.map_id]; exact le_sup_right, fun _ ↦ dpow_eq_of_mem_right' hIJ⟩

theorem dpow_eq_of_mem_left (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ I) :
      (IdealAdd.dividedPowers hIJ).dpow n x = hI.dpow n x :=
  dpow_eq_of_mem_left' hIJ hx

theorem dpow_eq_of_mem_right (hIJ : ∀ {n : ℕ}, ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a)
    {n : ℕ} {x : A} (hx : x ∈ J) :
    (IdealAdd.dividedPowers hIJ).dpow n x = hJ.dpow n x :=
  dpow_eq_of_mem_right' hIJ hx

/-- `I` as a `SubDPIdeal` of `I + K`. -/
noncomputable def subDPIdeal_left {K : Ideal A} {hK : DividedPowers K}
    (hIK : ∀ {n : ℕ}, ∀ a ∈ I ⊓ K, hI.dpow n a = hK.dpow n a) :
    SubDPIdeal (IdealAdd.dividedPowers hIK) where
  carrier           := I
  isSubideal c hc   := Ideal.mem_sup_left hc
  dpow_mem _ hn _ hj  := by
    rw [IdealAdd.dpow_eq_of_mem_left hIK hj]
    exact hI.dpow_mem hn hj

/-- `K` as a `SubDPIdeal` of `I + K`. -/
noncomputable def subDPIdeal_right {K : Ideal A} {hK : DividedPowers K}
    (hIK : ∀ {n : ℕ}, ∀ a ∈ I ⊓ K, hI.dpow n a = hK.dpow n a) :
    SubDPIdeal (IdealAdd.dividedPowers hIK) where
  carrier           := K
  isSubideal c hc   := Ideal.mem_sup_right hc
  dpow_mem _ hn _ hj  := by
    rw [IdealAdd.dpow_eq_of_mem_right hIK hj]
    exact hK.dpow_mem hn hj

open Ideal

variable {B : Type*} [CommRing B] [Algebra A B] {K : Ideal B} {hK : DividedPowers K}
    {hI' : DividedPowers (map (algebraMap A B) I)}

theorem dividedPowers_dpow_eq_algebraMap
    (hI'_ext : ∀ {n : ℕ} (a : A), hI'.dpow n ((algebraMap A B) a) = (algebraMap A B) (hI.dpow n a))
    (hI'_int : ∀ {n : ℕ}, ∀ b ∈ K ⊓ map (algebraMap A B) I, hK.dpow n b = hI'.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers hI'_int).dpow n ((algebraMap A B) a) =
      (algebraMap A B) (hI.dpow n a) := by
  rw [← hI'_ext]
  exact IdealAdd.dpow_eq_of_mem_right hI'_int (mem_map_of_mem (algebraMap A B) ha)

theorem dividedPowers_dpow_eq_algebraMap'
    (hI'_ext : hI.IsDPMorphism hI' (algebraMap A B))
    (h_int : ∀ {n : ℕ}, ∀ b ∈ map (algebraMap A B) I ⊓ K, hI'.dpow n b = hK.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers h_int).dpow n ((algebraMap A B) a) =
      (algebraMap A B) (hI.dpow n a) := by
  rw [← hI'_ext.2 _ ha]
  exact IdealAdd.dpow_eq_of_mem_left h_int (mem_map_of_mem (algebraMap A B) ha)


end IdealAdd

end DividedPowers
