/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPAlgebra.Exponential
import DividedPowers.DPAlgebra.Free
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.ForMathlib.Data.FinsetLemmas
import DividedPowers.ForMathlib.Data.Nat.Choose.Multinomial
import DividedPowers.ForMathlib.RingTheory.DividedPowers.Basic
import DividedPowers.ForMathlib.RingTheory.Localization.FractionRing
import DividedPowers.Padic
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology
import DividedPowers.ForMathlib.Algebra.TrivSqZeroExt
import DividedPowers.ForMathlib.RingTheory.GradedAlgebra.Basic

/-! # Construction of the divided power structure on the divided power algebra (work in progress)

In this file we construct the divided power structure on the universal divided power algebra
of a module. Our argument uses ideas present in [Roby-1965] (while avoiding the mistake in the
proof presented there), and is similar to the one sketched in the appendix of [BerthelotOgus-1978].

## Main definitions

* `DividedPowerAlgebra.Free.basis_grade`: the basis of the nth graded part of
  `DividedPowerAlgebra R M` associated with a basis of `M`.

* `DividedPowerAlgebra.Free.basis`: the basis of `DividedPowerAlgebra R M` associated with a basis
  of `M`.

* `DividedPowerAlgebra.Free.dpow`: the `dpow` function on the divided power algebra of a free
  module.

* `DividedPowerAlgebra.Free.dividedPowers`: the divided power structure on `augIdeal R M`,
  where `M` is a free `R`-module.

* `DividedPowerAlgebra.Presentation.dividedPowers`: the divided power structure on `augIdeal R M`
  associated with `p : Presentation R M`.

* `DividedPowerAlgebra.dividedPowers`: the divided power structure on `augIdeal R M`,
  where `M` is any `R`-module.

## Main results

* `DividedPowerAlgebra.onDPAlgebra_unique`: [Roby-1965, Lemma 2]: there is at most one divided
  power structure on the augmentation ideal of `DividedPowerAlgebra R M` such that
  `∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x`.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

-/

section

open DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

namespace DividedPowerAlgebra

universe u v v₁ v₂ w uA uR uS uM

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (x : M) {n : ℕ}

/-- Lemma 2 of Roby 65 : there is at most one divided power structure on the augmentation ideal
  of `DividedPowerAlgebra R M` such that `∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x`. -/
theorem onDPAlgebra_unique (h h' : DividedPowers (augIdeal R M))
    (h1 : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    (h1' : ∀ (n : ℕ) (x : M), h'.dpow n (ι R M x) = dp R n x) : h = h' := by
  apply DividedPowers.dpow_eq_from_gens h' h (augIdeal_eq_span R M)
  rintro n f ⟨q, hq : 0 < q, m, _, rfl⟩
  nth_rw 1 [← h1' q m]
  rw [← h1 q m, h.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m),
    h'.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m), h1 _ m, h1' _ m]

namespace Free

open Module

variable {R M} {ι : Type*} (b : Basis ι R M) {n : ℕ}

open scoped Nat

section cK

variable [DecidableEq ι] {n : ℕ} (k : Sym (ι →₀ ℕ) n) (s : Finset (ι →₀ ℕ))

/-- A combinatorial coefficient that appears in the definition of the divided power structure
of the divided power algebra. -/
noncomputable def cK : ℕ :=
  (k.val.sum.prod fun i _ ↦ Nat.multinomial s fun a ↦ (Multiset.count a ↑k • a) i) *
  (∏ d ∈ s, (Multiset.count d ↑k)! ^ (#d.support - 1) •
    ∏ i ∈ d.support, (Multiset.count d ↑k).uniformBell (d i))

variable {k s}

theorem cK_eq_of_subset {t : Finset (ι →₀ ℕ)} (hst : s ⊆ t) (hk : k ∈ s.sym n) :
    cK k s = cK k t := by
  have H0 (d) (hd : d ∉ s) : Multiset.count d ↑k = 0 := by
    simp only [mem_sym_iff] at hk
    simp only [Multiset.count_eq_zero, Sym.mem_coe]
    exact fun a ↦ hd (hk d a)
  unfold cK
  apply congr_arg₂
  · simp only [Finsupp.prod]
    apply Finset.prod_congr rfl
    intro i hi
    apply Nat.multinomial_congr_of_sdiff hst
    · intro d hd
      rw [mem_sdiff] at hd
      simp [H0 d hd.2]
    · simp
  · apply Finset.prod_subset_one_on_sdiff hst
    · intro d hd
      rw [mem_sdiff] at hd
      simp [H0 d hd.2, Nat.uniformBell_zero_left]
    · simp

theorem cK_map_single_eq_one {s : Finset ι} {k : Sym ι n} (hk : k  ∈ s.sym n) :
    let g : ι ↪ (ι →₀ ℕ) :=
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective Nat.one_ne_zero⟩
    cK (Sym.map g k) (s.map g) = 1 := by
  intro g
  simp only [cK, Sym.val_eq_coe, Sym.coe_map, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  convert mul_one _
  · apply Finset.prod_eq_one
    intro d hd
    simp only [mem_map] at hd
    obtain ⟨j, hj, rfl⟩ := hd
    rw [Multiset.count_map_eq_count' _ _ g.injective]
    convert mul_one _
    · apply Finset.prod_eq_one
      intro i hi
      have : i = j := by
        by_contra! h
        simp [g, Finsupp.single_eq_of_ne h] at hi
      simp [this, g, Nat.uniformBell_one_right]
    · suffices (g j).support = {j} by simp [this, card_singleton, tsub_self, pow_zero]
      ext i
      simp only [Finsupp.mem_support_iff, ne_eq, mem_singleton, g]
      by_cases h : i = j
      · simp [h]
      · simp [Finsupp.single_eq_of_ne h, h]
  · rw [eq_comm]
    simp only [Finsupp.prod]
    apply Finset.prod_eq_one
    intro i hi
    rw [← Nat.mul_right_inj, mul_one]
    convert Nat.multinomial_spec _ _
    · simp only [g] at hi
      simp only [prod_map, sum_map, Multiset.count_map_eq_count' _ _ g.injective]
      have H (j) (hj : i ≠ j) : Multiset.count j k * (g j) i = 0 := by
        simp [g, Finsupp.single_eq_of_ne hj]
      have H' (hi : i ∉ s) : Multiset.count i k * (g i) i = 0 := by
        convert zero_mul _
        simp only [Multiset.count_eq_zero, Sym.mem_coe]
        rw [mem_sym_iff] at hk
        exact fun a ↦ hi (hk i a)
      rw [Finset.prod_eq_single i _ _ , Finset.sum_eq_single i]
      · exact fun j hj hij ↦ H j (Ne.symm hij)
      · intro hi; rw [H' hi]
      · intro j hj hij
        rw [H j (Ne.symm hij), Nat.factorial_zero]
      · intro hi; rw [H' hi, Nat.factorial_zero]
    · intro H
      rw [Finset.prod_eq_zero_iff] at H
      obtain ⟨j, hj, h⟩ := H
      apply Nat.factorial_ne_zero _ h

theorem cK_zero {k : Sym (ι →₀ ℕ) 0} : cK k s = 1 := by
  simp [cK, Subsingleton.eq_zero k, Nat.uniformBell_zero_left]

theorem cK_one {k : Sym (ι →₀ ℕ) 1} : cK k s = 1 := by
  let d := Sym.oneEquiv.symm k
  have : k = Sym.oneEquiv d := by simp [d]
  have kval : (k : Multiset (ι →₀ ℕ)) = {d} := by simp [this]
  unfold cK
  rw [kval, Finset.prod_eq_single d]
  · simp
    constructor
    · apply Finset.prod_eq_one
      intro i hi
      have : Pi.single d (d i) = fun a ↦ if a = d then a i else 0 := by
        ext a
        split_ifs with h <;> simp [Pi.single_apply, h]
      simp [Multiset.nodup_singleton, Multiset.count_singleton, ← this, Nat.multinomial_single]
    · simp [Nat.uniformBell_one_left]
  · intro c hc hcd
    simp [Multiset.count_singleton, if_neg hcd, Nat.uniformBell_zero_left]
  · intros
    simp [Nat.uniformBell_one_left]

end cK

section DecidableEq

-- Decidability variables needed to define `dpow`
variable [DecidableEq R] [DecidableEq ι]

/-- The `dpow` function on the divided power algebra of a free module. -/
noncomputable def dpow (n : ℕ) (x : DividedPowerAlgebra R M) : DividedPowerAlgebra R M :=
  if x ∈ augIdeal R M then
    ∑ k ∈ ((basis R M b).repr x).support.sym n,
      cK k ((basis R M b).repr x).support •
        (∏ d ∈ ((basis R M b).repr x).support, ((basis R M b).repr x) d ^ Multiset.count d ↑k) •
            (basis R M b) k.val.sum
  else 0

theorem dpow_eq (H : DividedPowers (augIdeal R M))
    (hH : ∀ (n : ℕ) (x : M), H.dpow n (DividedPowerAlgebra.ι R M x) = dp R n x)
    {ι : Type*} [DecidableEq ι] (b : Basis ι R M) {n : ℕ} {x : DividedPowerAlgebra R M} :
    H.dpow n x = dpow b n x := by
  simp only [dpow]
  split_ifs with hx
  · nth_rewrite 1 [eq_of_basis b x]
    rw [H.dpow_linearCombination
      (fun _ hd ↦ basis_mem_augIdeal b (ne_zero_of_mem_support_of_mem_augIdeal b hx hd))]
    apply Finset.sum_congr rfl (fun k hk ↦ ?_)
    simp only [Finsupp.prod, Finset.prod_smul']
    set A := (∏ i ∈ ((basis R M b).repr x).support, ((basis R M b).repr x) i ^ Multiset.count i k)
    set B := ∏ i ∈ ((basis R M b).repr x).support, H.dpow (Multiset.count i k) ((basis R M b) i)
      with hB
    set C := (basis R M b k.val.sum) with hC
    suffices B = cK k ((basis R M b).repr x).support • C by simp [this]
    have (i) (hi : i ∈ ((basis R M b).repr x).support) :=
      dpow_basis_eq H hH b (Multiset.count i ↑k) i (ne_zero_of_mem_support_of_mem_augIdeal b hx hi)
    simp only [Finset.prod_congr rfl this, Finset.prod_smul', basis_prod,
      k.sum_eq_val_sum hk, ← hC] at hB
    simp only [hB, ← smul_assoc]
    apply congr_arg₂ _ _ rfl
    simp only [smul_eq_mul, Sym.val_eq_coe, Finsupp.coe_smul, Pi.smul_apply, cK]
    rw [mul_comm]
    apply congr_arg₂ _ rfl
    rw [Finset.prod_mul_distrib]
  · exact H.dpow_null hx

theorem dpow_eq_of_support_subset {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M)
    {s : Finset (ι →₀ ℕ)} (hs : ((basis R M b).repr x).support ⊆ s) :
    dpow b n x = ∑ k ∈ s.sym n, cK k s •
      (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d ↑k) • (basis R M b) k.val.sum := by
  simp only [dpow, if_pos hx]
  have Hs : ((basis R M b).repr x).support.sym n ⊆ s.sym n := fun k hk ↦ by
    simp only [mem_sym_iff] at hk ⊢
    exact fun a ha ↦ hs (hk a ha)
  have H0 (k) (hk : k ∈ ((basis R M b).repr x).support.sym n)
      (d) (hd : d ∉ ((basis R M b).repr x).support) :
      Multiset.count d ↑k = 0 := by
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hd
    simp only [mem_sym_iff, Finsupp.mem_support_iff, ne_eq] at hk
    exact Multiset.count_eq_zero.mpr (fun hd' ↦ hk d hd' hd)
  apply Finset.sum_subset_zero_on_sdiff Hs
  · intro k hk
    suffices (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d ↑k) = 0 by
      simp [this]
    simp [mem_sdiff] at hk
    obtain ⟨d, hd, hd'⟩ := hk.2
    rw [Finset.prod_eq_prod_diff_singleton_mul (hk.left d hd)]
    convert mul_zero _
    simp [hd']
    apply zero_pow
    simpa [Multiset.count_eq_zero]
  · intro k hk
    congr 1
    · apply cK_eq_of_subset hs hk
    congr 1
    apply Finset.prod_subset_one_on_sdiff hs
    · intro d hd
      rw [mem_sdiff] at hd
      rw [H0 k hk d hd.2, pow_zero]
    · intros; rfl

 theorem dpow_ι (m : M) : dpow b n (DividedPowerAlgebra.ι R M m) = dp R n m := by
  simp only [dpow, if_pos (ι_mem_augIdeal R M m)]
  have hm : m = ((b.repr m).sum fun i c ↦ c • b i) := by
    have := (Basis.linearCombination_repr b m).symm
    simpa only [Finsupp.linearCombination, Finsupp.lsum] using this
  let g : ι ↪ (ι →₀ ℕ) :=
    ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective Nat.one_ne_zero⟩
  let gg : Sym ι n ↪ Sym (ι →₀ ℕ) n := {
    toFun a := Sym.map g a
    inj' := Sym.map_injective g.injective _ }
  conv_rhs =>
    rw [hm]
    simp only [Finsupp.sum]
    rw [dp_sum _ (b.repr m).support n]
  set s := (b.repr m).support with hs
  set t := ((basis R M b).repr ((DividedPowerAlgebra.ι R M) m)).support with ht
  have hst : t = Finset.map g s := by
    simp only [← hs, ht, ι_repr_support_eq]
    congr
  have hst' : t.sym n = Finset.map gg (s.sym n) := hst ▸ Finset.sym_map _ _
  rw [hst', Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Function.Embedding.coeFn_mk, Sym.coe_map, Sym.val_eq_coe, gg, hst]
  rw [cK_map_single_eq_one hk, one_smul]
  simp only [prod_map, Multiset.count_map_eq_count' _ _ g.injective]
  have (x) (_ : x ∈ s) :
    ((basis R M b).repr ((DividedPowerAlgebra.ι R M) m)) (g x) ^ Multiset.count x k =
    (b.repr m) x ^ Multiset.count x ↑k := by
    conv_lhs => rw [hm, map_finsuppSum, map_finsuppSum]
    simp only [map_smul, Finsupp.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      ← basis_single_one_eq, Basis.repr_self]
    rw [Finsupp.sum_eq_single x]
    · simp only [Function.Embedding.coeFn_mk, Finsupp.single_eq_same, mul_one, g]
    · intro i hi hix
      convert mul_zero _
      rw [Finsupp.single_eq_of_ne]
      exact g.injective.ne_iff.mpr (Ne.symm hix)
    · simp
  rw [Finset.prod_congr rfl this]
  clear this
  have hk' :  (Multiset.map g k).sum = Multiset.toFinsupp (k : Multiset ι) := by
    symm
    rw [Multiset.toFinsupp_eq_iff]
    ext i
    simp only [Finsupp.count_toMultiset]
    set p : Multiset ι := ↑k with hp
    induction p using Multiset.induction_on with
    | empty => simp
    | cons j q H =>
      simp only [Multiset.count_cons, H, add_comm, Multiset.map_cons,
        Multiset.sum_cons, Finsupp.coe_add, Pi.add_apply, add_left_inj]
      simp [g, Finsupp.single_apply, eq_comm]
  simp only [hk', dp_smul, Finset.prod_smul']
  apply congr_arg₂ _ rfl
  simp [basis_eq, Finsupp.prod]
  have : (k : Multiset ι).toFinset ⊆ s := by
    intro i hi
    simp only [Multiset.mem_toFinset, Sym.mem_coe] at hi
    rw [mem_sym_iff] at hk
    exact hk i hi
  rw [← Finset.prod_sdiff this, eq_comm]
  convert one_mul _
  rw [Finset.prod_eq_one]
  intro i hi
  simp only [mem_sdiff, Multiset.mem_toFinset, Sym.mem_coe] at hi
  rw [← Sym.mem_coe, ← Multiset.count_eq_zero] at hi
  rw [hi.2, dp_zero]

theorem dpow_null {n : ℕ} {x : DividedPowerAlgebra R M} (hx : x ∉ augIdeal R M) :
    dpow b n x = 0 := by
  simp [dpow, hx]

theorem dpow_zero {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 0 x = 1 := by
  have : ↑(∅ : Sym (ι →₀ ℕ) 0) = 0 := rfl
  simp [dpow, if_pos hx, this, basis_eq, cK_zero]

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : dpow b n 0 = 0 := by
  simp [dpow, (Finset.sym_eq_empty (s := ∅) (n := n)).mpr, hn]

theorem dpow_mem {n : ℕ} {x : DividedPowerAlgebra R M} (hn : n ≠ 0) (hx : x ∈ augIdeal R M) :
    dpow b n x ∈ augIdeal R M := by
  have hn' : n = n.pred.succ := (Nat.succ_pred_eq_of_ne_zero hn).symm
  simp only [dpow]
  rw [if_pos, hn']
  apply Ideal.sum_mem
  intro k hk
  apply Submodule.smul_of_tower_mem
  obtain ⟨d, s', rfl⟩ := k.exists_eq_cons_of_succ
  simp only [Sym.mem_cons, mem_sym_iff, forall_eq_or_imp] at hk
  apply Submodule.smul_of_tower_mem
  apply basis_mem_augIdeal
  simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Sym.val_eq_coe, Sym.coe_cons,
    Multiset.sum_cons, ne_eq, add_eq_zero, ne_zero_of_mem_support_of_mem_augIdeal b hx hk.1,
    false_and, not_false_eq_true]
  exact hx

end DecidableEq
section Compare
/- The previous examples show that it is complicated to expand precisely the formulas
  to check the divided power structure, and in any case, it will end up in verifying
  specific combinatorial relations, which is undesireable.
  The following is another attempt, hopefully easier.
  The given formula for `dpow` is a prerequisite, though.
  It consists in doing *exactly* what one says when one describes the proof orally.
  To define a divided power structure on `DividedPowerAlgebra R M`,
  when `M` is a free `R`-module, we compare `dpow R M b`
  with `dpow S N c`, for a free `S`-module `N` with a basis `c` which is indexed
  by the same type as `b`.
  We have two possibilities
  * We embedd `R ↪ S`, and give ourselves `N` which is free with the “same” basis
    (`N := baseChange S N` could work) so that we know that we have a divided power
    structure on `DividedPowerAlgebra S N`.
    If `R` is an integral domain of characteristic `0`, one can take for `S` its fraction field
    and then the divided power structure exists.
    Since `R` embeds in `S`, the relations for `dpow R M b` follow from that of `dpow S N c`.
  * We view `R` as a quotient of `S`, `S →+* R`,
    and give ourselves `N` which is free with the “same” basis,
    and assume that we know that we have a divided power
    structure on `DividedPowerAlgebra S N`.
    The relations for `dpow S N c` imply that for `dpow R M b`. -/

variable {b} {S : Type*} [CommRing S] [Algebra R S] {N : Type*} [AddCommGroup N] [Module R N]
  [Module S N] [IsScalarTower R S N] {c : Basis ι S N} {f : M →ₗ[R] N} (hf : ∀ i, f (b i) = c i)
  (x : DividedPowerAlgebra R M) (d : ι →₀ ℕ)

section basis

include hf

lemma compare_basis : basis S N c d = LinearMap.lift S f (basis R M b d) := by
  simp [basis_eq, map_finsuppProd, LinearMap.lift_apply_dp, hf]

theorem repr_lift_eq :
    (basis S N c).repr (LinearMap.lift S f x) d = algebraMap R S ((basis R M b).repr x d) := by
  have : LinearMap.lift S f x =
      ((basis R M b).repr x).sum fun i r ↦ r • basis S N c i := by
    rw [eq_of_repr b x]
    simp [map_finsuppSum, compare_basis hf]
  rw [this, map_finsuppSum, Finsupp.sum_apply, Finsupp.sum_eq_single d]
  · simp [algebra_compatible_smul S]
  · intro e he hed
    simp [algebra_compatible_smul S, Finsupp.single_eq_of_ne (Ne.symm hed)]
  · simp

theorem repr_lift_support_subset :
    ((basis S N c).repr (LinearMap.lift S f x)).support ⊆ ((basis R M b).repr x).support := by
  intro d
  simp [Finsupp.mem_support_iff, repr_lift_eq hf, not_imp_not]
  intro H
  rw [H, map_zero]

variable {x}

theorem lift_mem_augIdeal (hx : x ∈ augIdeal R M) : LinearMap.lift S f x ∈ augIdeal S N := by
  classical
  rw [mem_augIdeal_iff_of_repr c]
  rw [mem_augIdeal_iff_of_repr b] at hx
  simp [repr_lift_eq hf, hx]

variable [DecidableEq ι] [DecidableEq R] [DecidableEq S]

theorem lift_dpow (hx : x ∈ augIdeal R M) :
    LinearMap.lift S f (dpow b n x) = dpow c n (LinearMap.lift S f x) := by
  rw [dpow_eq_of_support_subset b hx (subset_refl _),
    dpow_eq_of_support_subset c (lift_mem_augIdeal hf hx) (repr_lift_support_subset hf x)]
  simp only [nsmul_eq_mul, Algebra.mul_smul_comm]
  simp [algebra_compatible_smul S, repr_lift_eq hf, compare_basis hf]

theorem lift_dpow_of_lift_eq_zero (hx : x ∈ augIdeal R M) (hx' : LinearMap.lift S f x = 0)
    (hn : n ≠ 0) : LinearMap.lift S f (dpow b n x) = 0 := by
  rw [lift_dpow hf hx, hx', dpow_eval_zero _ hn]

end basis

end Compare

namespace CharZero

variable (R) in
/-- Notation for the fraction ring of `R`. -/
abbrev S := FractionRing R

variable (ι R) in
/-- Notation for the type `ι →₀ (S R)`. -/
abbrev N := ι →₀ (S R)

private noncomputable abbrev c : Basis ι (S R) (N R ι) := Finsupp.basisSingleOne

private noncomputable abbrev f : M →ₗ[R] (N R ι) := Basis.constr b (S R) c

lemma hf (i : ι) : f b (b i) = c i  := by simp [c, f]

local instance : IsScalarTower R (S R) (N R ι) := Finsupp.isScalarTower ι (S R)

theorem lift_injective : Function.Injective (LinearMap.lift (S R) (f b)) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  rw [Basis.ext_elem_iff (basis (S R) (N R ι) c)] at hx
  rw [Basis.ext_elem_iff (basis R M b)]
  intro d
  specialize hx d
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply] at hx ⊢
  simpa [repr_lift_eq (hf b) x] using hx

theorem augIdeal_map_lift_eq :
    (augIdeal R M).map (LinearMap.lift (S R) (f b)) = augIdeal (S R) (N R ι) := by
  classical
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_augIdeal_iff_of_repr c]
    rw [mem_augIdeal_iff_of_repr b] at hx
    simp [repr_lift_eq (hf b), hx]
  · intro x hx
    rw [mem_augIdeal_iff_of_repr c] at hx
    rw [eq_of_repr c x]
    simp only [Finsupp.sum]
    apply Ideal.sum_mem
    intro d hd
    rw [Finsupp.mem_support_iff] at hd
    rw [Algebra.smul_def]
    apply Ideal.mul_mem_left
    rw [compare_basis (hf b)]
    apply Ideal.mem_map_of_mem
    simp only [mem_augIdeal_iff_of_repr b, Basis.repr_self]
    rw [Finsupp.single_eq_of_ne]
    intro hd'
    apply hd
    rw [← hd', hx]

variable [CharZero R] [IsDomain R]

/-- The `ℚ`-algebra structure on `S R`. -/
noncomputable local instance : Algebra ℚ (S R) :=
  RingHom.toAlgebra (IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom _) (by
    intro y
    refine IsFractionRing.isUnit_map_of_injective ?_ y
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [← Int.cast_eq_zero (α := R), ← (FaithfulSMul.algebraMap_injective R (S R)).eq_iff]
    simpa using ha))

variable [DecidableEq R]

/-- Notation for the divided power structure on the augmentation ideal of
  `(DividedPowerAlgebra (S R) (N R ι))`. -/
noncomputable abbrev hSN  : DividedPowers (augIdeal (S R) (N R ι)) :=
  RatAlgebra.dividedPowers (augIdeal (S R) (N R ι))

variable [DecidableEq ι]

theorem lift_dpow_eq_dpow_lift (n : ℕ) {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    LinearMap.lift (S R) (f b) (dpow b n x) =
      hSN.dpow n ((LinearMap.lift (S R) (f b)) x) :=  by
  rw [dpow_eq _ ?_ c]
  apply lift_dpow (hf b) hx -- (by exact hf b) x hx
  intro n x
  rw [RatAlgebra.dpow_eq_inv_fact_smul _ _ (ι_mem_augIdeal _ _ x)]
  simp only [Ring.inverse_eq_inv', DividedPowerAlgebra.ι, LinearMap.coe_mk, AddHom.coe_mk]
  have : Invertible (n ! : ℚ) := invertibleOfNonzero (by simp [Nat.factorial_ne_zero])
  rw [← invOf_eq_inv, invOf_smul_eq_iff, ← natFactorial_mul_dp_eq]
  simp [Algebra.smul_def]

/-- The divided power structure on the divided power algebra of a free module
over a characteristic zero domain -/
noncomputable def dividedPowers : DividedPowers (augIdeal R M) :=
  ofInjective (augIdeal R M) (augIdeal (S R) (N R ι))
    (LinearMap.lift (S R) (f b)) (lift_injective b) (hSN) (augIdeal_map_lift_eq b)
    (fun n x hx ↦ ⟨dpow b n x, fun hn ↦ dpow_mem b hn hx, lift_dpow_eq_dpow_lift _ _ hx⟩)

theorem dpow_eq (x : DividedPowerAlgebra R M) :
    (dividedPowers b).dpow n x = dpow b n x := by
  simp only [CharZero.dividedPowers, ofInjective]
  simp only [RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, dite_eq_ite]
  split_ifs with hx
  · rw [← lift_dpow_eq_dpow_lift, ← (lift_injective b).eq_iff]
    · exact Function.apply_invFun_apply
    · exact hx
  · rw [dpow_null b hx]

theorem dpow_ι_eq_dp (n : ℕ) (x : M) :
    (dividedPowers b).dpow n (DividedPowerAlgebra.ι R M x) = dp R n x := by
  rw [dpow_eq, dpow_ι]

end CharZero

section Quotient

noncomputable section

variable (R) in
private def MvPoly_dividedPowers [DecidableEq R] [DecidableEq ι] :
    DividedPowers (augIdeal (MvPolynomial R ℤ) (ι →₀ (MvPolynomial R ℤ))) :=
  CharZero.dividedPowers Finsupp.basisSingleOne

/-- The `(MvPolynomial R ℤ)`-module structure on `R`. -/
local instance : Module (MvPolynomial R ℤ) M :=
  Module.compHom M (MvPolynomial.eval₂Hom (Int.castRingHom R) id)

/-- The `(MvPolynomial R ℤ)`-algebra structure on `R`. -/
local instance : Algebra (MvPolynomial R ℤ) R :=
  RingHom.toAlgebra (MvPolynomial.eval₂Hom (Int.castRingHom R) id)

local instance : IsScalarTower (MvPolynomial R ℤ) R M :=
  IsScalarTower.of_algebraMap_smul fun _ ↦ congrFun rfl

private def f : (ι →₀ MvPolynomial R ℤ) →ₗ[MvPolynomial R ℤ] M :=
  Finsupp.linearCombination (MvPolynomial R ℤ) (fun i ↦ b i)

private lemma f_apply (i : ι) : (f b) (Finsupp.basisSingleOne i) = b i := by
    simp only [f]
    rw [Finsupp.coe_basisSingleOne, Finsupp.linearCombination_single, one_smul]

private lemma lift_f (d : ι →₀ ℕ) :
    (LinearMap.lift R (f b))
      (basis (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) Finsupp.basisSingleOne d) =
    basis R M b d := by
  simp only [basis_eq, map_finsuppProd, LinearMap.lift_apply_dp]
  apply Finsupp.prod_congr
  intros; rw [f_apply]

variable [DecidableEq R]

private def φ : R → (MvPolynomial R ℤ) := fun r ↦ if r = 0 then 0 else MvPolynomial.X r

lemma algebraMap_φ (r : R) : algebraMap (MvPolynomial R ℤ) R (φ r) = r := by
    simp only [RingHom.algebraMap_toAlgebra, φ]
    split_ifs with hr
    · simp [hr]
    · rw [MvPolynomial.coe_eval₂Hom]; simp

private def toN (x : DividedPowerAlgebra R M) :
    DividedPowerAlgebra (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) :=
  Finsupp.linearCombination (MvPolynomial R ℤ)
    (basis (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) Finsupp.basisSingleOne)
    (((basis R M b).repr x).mapRange φ (by simp [φ]))

lemma toN_repr (x : DividedPowerAlgebra R M) (d : ι →₀ ℕ) :
      ((basis (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) Finsupp.basisSingleOne).repr
        (toN b x) d) = φ ((basis R M b).repr x d) := by
    simp only [toN]
    simp [Finsupp.linearCombination, Finsupp.lsum, map_finsuppSum]

lemma toNx {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    toN b x ∈ augIdeal (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ) := by
  rw [mem_augIdeal_iff_of_repr Finsupp.basisSingleOne]
  rw [mem_augIdeal_iff_of_repr b] at hx
  simp [toN_repr, hx, φ]

private lemma id_eq_lift_toN (x : DividedPowerAlgebra R M) :
    x = LinearMap.lift R (f b) (toN b x) := by
  apply Basis.ext_elem (basis R M b)
  intro d
  simp only [toN, Finsupp.linearCombination, Finsupp.coe_lsum, LinearMap.coe_smulRight,
    LinearMap.id_coe, id_eq, map_finsuppSum, map_smul, Finsupp.sum_apply]
  simp only [lift_f, algebra_compatible_smul R, Algebra.algebraMap_self,
    RingHomCompTriple.comp_apply, map_smul, Basis.repr_self, Finsupp.coe_smul, Pi.smul_apply]
  rw [Finsupp.sum_eq_single d]
  · simp only [Finsupp.mapRange_apply, Finsupp.single_eq_same,φ]
    split_ifs with hd
    · simp [hd]
    · simp [RingHom.algebraMap_toAlgebra]
  · intro _ _ hed; simp [Finsupp.single_eq_of_ne (Ne.symm hed)]
  · simp

variable [DecidableEq ι]

lemma lift_dpow_eq_of_lift_eq {u v : DividedPowerAlgebra (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ)}
    (hu : u ∈ augIdeal (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ))
    (hv : v ∈ augIdeal (MvPolynomial R ℤ) (ι →₀ MvPolynomial R ℤ))
    (huv : LinearMap.lift R (f b) u = LinearMap.lift R (f b) v) :
    LinearMap.lift R (f b) (dpow Finsupp.basisSingleOne n u) =
      LinearMap.lift R (f b) (dpow Finsupp.basisSingleOne n v) := by
  rw [lift_dpow (f_apply b) hu, lift_dpow (f_apply b) hv, huv]

variable {m n : ℕ} {a x y : DividedPowerAlgebra R M}

theorem dpow_add (hx : x ∈ augIdeal R M) (hy : y ∈ augIdeal R M) :
    dpow b n (x + y) = ∑ k ∈ Finset.antidiagonal n, dpow b k.1 x * dpow b k.2 y := by
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, id_eq_lift_toN b y, ← map_add,
    ← lift_dpow (f_apply b) (Ideal.add_mem _ (toNx b hx) (toNx b hy)),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.dpow_add _ (toNx b hx) (toNx b hy)]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [dpow_eq _ (CharZero.dpow_ι_eq_dp c) c]
  rw [lift_dpow (f_apply b) (toNx b hx), ← id_eq_lift_toN b x,
    lift_dpow (f_apply b) (toNx b hy), ← id_eq_lift_toN b y]

theorem dpow_sum {α : Type*} [DecidableEq α] (x : α → DividedPowerAlgebra R M) {s : Finset α}
    (hx : ∀ a ∈ s, x a ∈ augIdeal R M) :
    dpow b n (∑ a ∈ s, x a) = ∑ k ∈ s.sym n, ∏ d ∈ s, dpow b (Multiset.count d ↑k) (x d) :=
  DividedPowers.dpow_sum' (dpow b) (fun a ↦ dpow_zero b a) (fun a a_1 ↦ dpow_add b a a_1)
    (fun a ↦ dpow_eval_zero b a) hx

theorem dpow_mul (hx : x ∈ augIdeal R M) : dpow b n (a * x) = a ^ n * dpow b n x := by
  classical
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b a, id_eq_lift_toN b x, ← map_mul,
    ← lift_dpow (f_apply b) (Ideal.mul_mem_left _ _ (toNx b hx)),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.dpow_mul _ (toNx b hx), map_mul,
    map_pow, dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, ← id_eq_lift_toN b a,
    lift_dpow (f_apply b) (toNx b hx), ← id_eq_lift_toN b x]

theorem mul_dpow (hx : x ∈ augIdeal R M) :
    dpow b m x * dpow b n x = ↑((m + n).choose m) * dpow b (m + n) x := by
  classical
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, ← lift_dpow (f_apply b) (toNx b hx),
    ← lift_dpow (f_apply b) (toNx b hx), ← map_mul, ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c,
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.mul_dpow _ (toNx b hx),
    map_mul, map_natCast, dpow_eq _ (CharZero.dpow_ι_eq_dp c) c,
    lift_dpow (f_apply b) (toNx b hx)]

theorem dpow_comp (hn : n ≠ 0) (hx : x ∈ augIdeal R M) :
    dpow b m (dpow b n x) = ↑(m.uniformBell n) * dpow b (m * n) x := by
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, ← lift_dpow (f_apply b) (toNx b hx),
    ← lift_dpow (f_apply b) (dpow_mem _ hn ((toNx b hx))),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c,
    DividedPowers.dpow_comp _ hn (toNx b hx), map_mul, map_natCast,
    dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, lift_dpow (f_apply b) (toNx b hx)]

theorem dpow_one {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M) :
    dpow b 1 x = x := by
  let c : Basis ι (MvPolynomial R ℤ) (ι →₀ _) := Finsupp.basisSingleOne
  rw [id_eq_lift_toN b x, ← lift_dpow (f_apply b) (toNx b hx),
    ← dpow_eq _ (CharZero.dpow_ι_eq_dp c) c, DividedPowers.dpow_one _ (toNx b hx)]

/-- The divided power structure on `augIdeal R M`, where `M` is a free `R`-module. -/
def dividedPowers : DividedPowers (augIdeal R M) where
  dpow := dpow b
  dpow_null := dpow_null b
  dpow_zero := dpow_zero b
  dpow_one := dpow_one b
  dpow_mem := dpow_mem b
  dpow_add := dpow_add b
  dpow_mul := dpow_mul b
  mul_dpow := mul_dpow b
  dpow_comp := dpow_comp b

theorem dpow_eq_dp (n : ℕ) (x : M) :
    (dividedPowers b).dpow n (DividedPowerAlgebra.ι R M x) = dp R n x := by
  simp [dividedPowers, dpow_ι]

end

end Quotient

end Free

section General

variable {M} {L : Type*} [AddCommGroup L] [Module R L] {f : L →ₗ[R] M}

theorem isSubDPIdeal_of_isSurjective [DecidableEq R] (hL : DividedPowers (augIdeal R L))
    (dpow_eq_dp : ∀ (n : ℕ) (x : L), hL.dpow n (ι R L x) = dp R n x) (hf : Function.Surjective f) :
    hL.IsSubDPIdeal (RingHom.ker (LinearMap.lift R f)) := by
  rw [LinearMap.ker_lift_of_surjective f hf, kerLift, hL.span_isSubDPIdeal_iff]
  · rintro n hn _ ⟨⟨⟨q, hq⟩, ⟨l, hl⟩⟩, rfl⟩
    simp only [PNat.mk_coe]
    rw [← dpow_eq_dp, hL.dpow_comp (Nat.ne_zero_of_lt hq) (ι_mem_augIdeal R L l)]
    apply Ideal.mul_mem_left
    apply Ideal.subset_span
    rw [dpow_eq_dp]
    exact ⟨(⟨n * q, Nat.mul_pos (Nat.zero_lt_of_ne_zero hn) hq⟩, ⟨l, hl⟩), rfl⟩
  · rintro _ ⟨⟨⟨q, hq⟩, ⟨l, hl⟩⟩, rfl⟩
    simp only [PNat.mk_coe, SetLike.mem_coe]
    exact dp_mem_augIdeal R L hq l

noncomputable section

variable (M) in
/-- A presentation of a module by a free module with a basis. -/
structure _root_.Module.Presentation where
    /-- A set `s` of elements in `M`. -/
    s : Set M
    /-- The underlying type `L` for the free module. -/
    L : Type*
    dec_s : DecidableEq s
    /-- The commutative additive group structure on `L`. -/
    acgL : AddCommGroup L
    /-- The `R`-module structure on `L`. -/
    mRL : Module R L
    /-- An `R`-basis of `L` indexed by the set `s`. -/
    b : Module.Basis s R L
    /-- An `R`-linear map from the free `R`-module `L` to `M`. -/
    f : L →ₗ[R] M
    /-- Surjectivity of `f`. -/
    surj : Function.Surjective f

open Module

variable (M) in
/-- The basic presentation of a module. -/
def presentation [DecidableEq M] : Presentation R M where
  s      := (Set.univ : Set M)
  L      := Set.univ →₀ R
  dec_s  := inferInstance
  acgL   := inferInstance
  mRL    := inferInstance
  b      := Finsupp.basisSingleOne
  f      := Finsupp.linearCombination R (fun m ↦ (m : M))
  surj m := ⟨Finsupp.single ⟨m, Set.mem_univ m⟩ 1, by simp [Finsupp.linearCombination_single]⟩

namespace Presentation

variable {R} [DecidableEq R] (hL : DividedPowers (augIdeal R L)) (p : Presentation R M)

private instance : AddCommGroup p.L := p.acgL

private instance : Module R p.L := p.mRL

private instance : Module.Free R p.L := Module.Free.of_basis p.b

private instance : DecidableEq p.s := p.dec_s

theorem isSubDPIdeal :
    IsSubDPIdeal (Free.dividedPowers p.b)
      (RingHom.ker (LinearMap.lift R p.f).toRingHom ⊓ augIdeal R p.L) := by
  apply IsSubDPIdeal.mk (by simp)
  · intro n hn x hx
    simp only [AlgHom.toRingHom_eq_coe, Ideal.mem_inf, RingHom.mem_ker, RingHom.coe_coe] at hx
    exact ⟨(isSubDPIdeal_of_isSurjective R (Free.dividedPowers p.b) (Free.dpow_eq_dp p.b) p.surj).dpow_mem
      n hn hx.1, dpow_mem _ hn hx.2⟩

def dividedPowers : DividedPowers (augIdeal R M) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers (Free.dividedPowers p.b)
    (LinearMap.lift_surjective p.surj) (LinearMap.augIdeal_map_lift R p.L p.f p.surj).symm
    (isSubDPIdeal p)

theorem dpow_eq_dp (n : ℕ) (x : M) : (dividedPowers p).dpow n (ι R M x) = dp R n x := by
  simp only [dividedPowers]
  obtain ⟨y, rfl⟩ := p.surj x
  rw [← LinearMap.lift_ι_apply]
  erw [Quotient.OfSurjective.dpow_apply (Free.dividedPowers p.b)
    (LinearMap.lift_surjective p.surj) (LinearMap.augIdeal_map_lift R p.L p.f p.surj).symm
    (isSubDPIdeal p) (ι_mem_augIdeal _ _ y) (n := n)]
  simp [Free.dpow_eq_dp p.b, LinearMap.lift_apply_dp]

end Presentation

variable [DecidableEq R] [DecidableEq M]

variable (M) in
/-- The canonical divided powers structure on the universal divided power algebra. -/
def dividedPowers : DividedPowers (augIdeal R M) := Presentation.dividedPowers (presentation R M)

theorem dpow_eq_dp (n : ℕ) (x : M) : (dividedPowers R M).dpow n (ι R M x) = dp R n x :=
  Presentation.dpow_eq_dp (presentation R M) n x

end

end General

section Unused

-- I think we could remove this section.

open DividedPowerAlgebra.Free Module

variable {R M} {ι : Type*} (b : Basis ι R M) {n : ℕ} [DecidableEq R] [DecidableEq ι]

/-- The exponential power series associated with `dpow` -/
noncomputable def dpowExp (x : DividedPowerAlgebra R M) : PowerSeries (DividedPowerAlgebra R M) :=
  PowerSeries.mk (fun n ↦ dpow b n x)

open scoped PowerSeries.WithPiTopology

local instance : UniformSpace (DividedPowerAlgebra R M) := ⊥

local instance : DiscreteTopology (DividedPowerAlgebra R M) := by
    exact forall_open_iff_discrete.mp fun s ↦ trivial

theorem dpowExp_eq_of_support_subset {x : DividedPowerAlgebra R M} (hx : x ∈ augIdeal R M)
    {s : Finset (ι →₀ ℕ)} (hs : ((basis R M b).repr x).support ⊆ s) :
    dpowExp b x = ∑' (n : ℕ), ∑ k ∈ s.sym n,
      (∏ d ∈ s, ((basis R M b).repr x) d ^ Multiset.count d k) •
        (PowerSeries.monomial n) ((cK k s) * (basis R M b) (k : Multiset (ι →₀ ℕ)).sum) := by
  rw [PowerSeries.as_tsum (dpowExp b x)]
  simp [dpowExp, dpow_eq_of_support_subset b hx hs, Sym.val_eq_coe, nsmul_eq_mul,
    Algebra.mul_smul_comm, PowerSeries.coeff_mk, map_sum, LinearMap.map_smul_of_tower]

end Unused

end DividedPowerAlgebra
