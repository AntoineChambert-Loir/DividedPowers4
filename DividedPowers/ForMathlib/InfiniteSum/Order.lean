/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module infinite_sum.order
-/
import DividedPowers.ForMathlib.InfiniteSum.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.MonotoneConvergence

/-!
# Infinite sums and products in an order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides lemmas about the interaction of infinite sums and order operations.
-/


open Finset Filter Function

open scoped BigOperators Classical

variable {ι κ α : Type _}

section Preorder

variable [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [T2Space α] {f : ℕ → α} {c : α}

variable [CommMonoid α]

@[to_additive tsum_le_of_sum_range_le]
theorem tprod_le_of_prod_range_le (hf : Multipliable f) (h : ∀ n, ∏ i in range n, f i ≤ c) :
    ∏' n, f n ≤ c :=
  let ⟨_, hl⟩ := hf
  hl.tprod_eq.symm ▸ le_of_tendsto' hl.tendsto_sum_nat h
#align tprod_le_of_prod_range_le tprod_le_of_prod_range_le
#align tsum_le_of_sum_range_le tsum_le_of_sum_range_le

end Preorder

section OrderedCommMonoid

variable [OrderedCommMonoid α]

variable [TopologicalSpace α] [OrderClosedTopology α] {f g : ι → α} {a a₁ a₂ : α}

@[to_additive]
theorem hasProd_le (h : ∀ i, f i ≤ g i) (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto' hf hg fun _ => prod_le_prod' fun i _ => h i
#align has_prod_le hasProd_le
#align has_sum_le hasSum_le

@[to_additive, mono]
theorem hasProd_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
  hasProd_le h hf hg
#align has_prod_mono hasProd_mono
#align has_sum_mono hasSum_mono

@[to_additive]
theorem hasProd_le_of_prod_le (hf : HasProd f a) (h : ∀ s, ∏ i in s, f i ≤ a₂) : a ≤ a₂ :=
  le_of_tendsto' hf h
#align has_prod_le_of_prod_le hasProd_le_of_prod_le
#align has_sum_le_of_sum_le hasSum_le_of_sum_le

@[to_additive]
theorem le_hasProd_of_le_prod (hf : HasProd f a) (h : ∀ s, a₂ ≤ ∏ i in s, f i) : a₂ ≤ a :=
  ge_of_tendsto' hf h
#align le_has_prod_of_le_prod le_hasProd_of_le_prod
#align le_has_sum_of_le_sum le_hasSum_of_le_sum

/- rw [← hasSum_extend_zero he] at hf
  refine hasSum_le (fun c => ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h-/

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (c «expr ∉ » set.range[set.range] e) -/
@[to_additive]
theorem hasProd_le_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ (c) (_ : c ∉ Set.range e), 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : HasProd f a₁)
    (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  rw [← hasProd_extend_one he] at hf
  refine hasProd_le (fun c => ?_) hf hg
  obtain ⟨i, rfl⟩ | h := em (c ∈ Set.range e)
  · rw [he.extend_apply]
    exact h _
  · rw [extend_apply' _ _ _ h]
    exact hs _ h
#align has_prod_le_inj hasProd_le_inj
#align has_sum_le_inj hasSum_le_inj

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (c «expr ∉ » set.range[set.range] e) -/
@[to_additive tsum_le_tsum_of_inj]
theorem tprod_le_tprod_of_inj {g : κ → α} (e : ι → κ) (he : Injective e)
    (hs : ∀ (c) (_ : c ∉ Set.range e), 1 ≤ g c) (h : ∀ i, f i ≤ g (e i)) (hf : Multipliable f)
    (hg : Multipliable g) : tprod f ≤ tprod g :=
  hasProd_le_inj _ he hs h hf.hasProd hg.hasProd
#align tprod_le_tprod_of_inj tprod_le_tprod_of_inj
#align tsum_le_tsum_of_inj tsum_le_tsum_of_inj

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (i «expr ∉ » s) -/
@[to_additive]
theorem prod_le_hasProd (s : Finset ι) (hs : ∀ (i) (_ : i ∉ s), 1 ≤ f i) (hf : HasProd f a) :
    ∏ i in s, f i ≤ a :=
  ge_of_tendsto hf
    (eventually_atTop.2
      ⟨s, fun _ hst => prod_le_prod_of_subset_of_one_le' hst fun i _ hbs => hs i hbs⟩)
#align prod_le_has_prod prod_le_hasProd
#align sum_le_has_sum sum_le_hasSum

@[to_additive]
theorem isLUB_hasProd (h : ∀ i, 1 ≤ f i) (hf : HasProd f a) :
    IsLUB (Set.range fun s => ∏ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.prod_mono_set_of_one_le' h) hf
#align is_lub_has_prod isLUB_hasProd
#align is_lub_has_sum isLUB_hasSum

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b' «expr ≠ » i) -/
@[to_additive]
theorem le_hasProd (hf : HasProd f a) (i : ι) (hb : ∀ (b') (_ : b' ≠ i), 1 ≤ f b') : f i ≤ a :=
  calc
    f i = ∏ i in {i}, f i := (Finset.prod_singleton _ _).symm
    _ ≤ a := prod_le_hasProd _ (by convert hb; simp) hf
#align le_has_prod le_hasProd
#align le_has_sum le_hasSum

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (i «expr ∉ » s) -/
@[to_additive sum_le_tsum]
theorem prod_le_tprod {f : ι → α} (s : Finset ι) (hs : ∀ (i) (_ : i ∉ s), 1 ≤ f i)
    (hf : Multipliable f) : ∏ i in s, f i ≤ ∏' i, f i :=
  prod_le_hasProd s hs hf.hasProd
#align prod_le_tprod prod_le_tprod
#align sum_le_tsum sum_le_tsum

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (b' «expr ≠ » i) -/
@[to_additive le_tsum]
theorem le_tprod (hf : Multipliable f) (i : ι) (hb : ∀ (b') (_ : b' ≠ i), 1 ≤ f b') :
    f i ≤ ∏' i, f i :=
  le_hasProd (Multipliable.hasProd hf) i hb
#align le_tprod le_tprod
#align le_tsum le_tsum

@[to_additive tsum_le_tsum]
theorem tprod_le_tprod (h : ∀ i, f i ≤ g i) (hf : Multipliable f) (hg : Multipliable g) :
    ∏' i, f i ≤ ∏' i, g i :=
  hasProd_le h hf.hasProd hg.hasProd
#align tprod_le_tprod tprod_le_tprod
#align tsum_le_tsum tsum_le_tsum

@[to_additive tsum_mono, mono]
theorem tprod_mono (hf : Multipliable f) (hg : Multipliable g) (h : f ≤ g) :
    ∏' n, f n ≤ ∏' n, g n :=
  tprod_le_tprod h hf hg
#align tprod_mono tprod_mono
#align tsum_mono tsum_mono

@[to_additive tsum_le_of_sum_le]
theorem tprod_le_of_prod_le (hf : Multipliable f) (h : ∀ s, ∏ i in s, f i ≤ a₂) : ∏' i, f i ≤ a₂ :=
  hasProd_le_of_prod_le hf.hasProd h
#align tprod_le_of_prod_le tprod_le_of_prod_le
#align tsum_le_of_sum_le tsum_le_of_sum_le

@[to_additive tsum_le_of_sum_le']
theorem tprod_le_of_prod_le' (ha₂ : 1 ≤ a₂) (h : ∀ s, ∏ i in s, f i ≤ a₂) : ∏' i, f i ≤ a₂ :=
  by
  by_cases hf : Multipliable f
  · exact tprod_le_of_prod_le hf h
  · rw [tprod_eq_one_of_not_multipliable hf]
    exact ha₂
#align tprod_le_of_prod_le' tprod_le_of_prod_le'
#align tsum_le_of_sum_le' tsum_le_of_sum_le'

@[to_additive]
theorem HasProd.one_le (h : ∀ i, 1 ≤ g i) (ha : HasProd g a) : 1 ≤ a :=
  hasProd_le h hasProd_one ha
#align has_prod.one_le HasProd.one_le
#align has_sum.nonneg HasSum.nonneg

@[to_additive]
theorem HasProd.le_one (h : ∀ i, g i ≤ 1) (ha : HasProd g a) : a ≤ 1 :=
  hasProd_le h ha hasProd_one
#align has_prod.le_one HasProd.le_one
#align has_sum.nonpos HasSum.nonpos

@[to_additive]
theorem tprod_one_le (h : ∀ i, 1 ≤ g i) : 1 ≤ ∏' i, g i :=
  by
  by_cases hg : Multipliable g
  · exact hg.hasProd.one_le h
  · simp [tprod_eq_one_of_not_multipliable hg]
#align tprod_one_le tprod_one_le
#align tprod_nonneg tprod_nonneg

@[to_additive tsum_nonpos]
theorem tprod_le_one (h : ∀ i, f i ≤ 1) : ∏' i, f i ≤ 1 :=
  by
  by_cases hf : Multipliable f
  · exact hf.hasProd.le_one h
  · simp [tprod_eq_one_of_not_multipliable hf]
#align tprod_le_one tprod_le_one
#align tsum_nonpos tsum_nonpos

end OrderedCommMonoid

section OrderedCommGroup

variable [TopologicalSpace α]

variable [OrderedCommGroup α] [TopologicalGroup α] [OrderClosedTopology α]

variable {f g : ι → α} {a₁ a₂ : α} {i : ι}

@[to_additive]
theorem hasProd_lt (h : f ≤ g) (hi : f i < g i) (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ < a₂ :=
  by
  have : update f i 1 ≤ update g i 1 := update_le_update_iff.mpr ⟨rfl.le, fun i _ => h i⟩
  have : 1 / f i * a₁ ≤ 1 / g i * a₂ := hasProd_le this (hf.update i 1) (hg.update i 1)
  simpa only [one_div, mul_inv_cancel_left] using mul_lt_mul_of_lt_of_le hi this
#align has_prod_lt hasProd_lt
#align has_sum_lt hasSum_lt

@[to_additive, mono]
theorem hasProd_strict_mono (hf : HasProd f a₁) (hg : HasProd g a₂) (h : f < g) : a₁ < a₂ :=
  let ⟨hle, _, hi⟩ := Pi.lt_def.mp h
  hasProd_lt hle hi hf hg
#align has_prod_strict_mono hasProd_strict_mono
#align has_sum_strict_mono hasSum_strict_mono

@[to_additive tsum_lt_tsum]
theorem tprod_lt_tprod (h : f ≤ g) (hi : f i < g i) (hf : Multipliable f) (hg : Multipliable g) :
    ∏' n, f n < ∏' n, g n :=
  hasProd_lt h hi hf.hasProd hg.hasProd
#align tprod_lt_tprod tprod_lt_tprod
#align tsum_lt_tsum tsum_lt_tsum

@[to_additive tsum_strict_mono, mono]
theorem tprod_strict_mono (hf : Multipliable f) (hg : Multipliable g) (h : f < g) :
    ∏' n, f n < ∏' n, g n :=
  let ⟨hle, _, hi⟩ := Pi.lt_def.mp h
  tprod_lt_tprod hle hi hf hg
#align tprod_strict_mono tprod_strict_mono
#align tsum_strict_mono tsum_strict_mono

@[to_additive tsum_one_lt]
theorem tprod_pos (hprod : Multipliable g) (hg : ∀ i, 1 ≤ g i) (i : ι) (hi : 1 < g i) :
    1 < ∏' i, g i := by rw [← tprod_one]; exact tprod_lt_tprod hg hi multipliable_one hprod
#align tprod_pos tprod_pos
#align tsum_one_lt tsum_one_lt

@[to_additive]
theorem hasProd_one_iff_of_one_le (hf : ∀ i, 1 ≤ f i) : HasProd f 1 ↔ f = 1 :=
  by
  refine' ⟨fun hf' => _, _⟩
  · ext i
    refine' (hf i).eq_of_not_gt fun hi => _
    simpa using hasProd_lt hf hi hasProd_one hf'
  · rintro rfl
    exact hasProd_one
#align has_prod_one_iff_of_one_le hasProd_one_iff_of_one_le
#align has_sum_zero_iff_of_nonneg hasSum_zero_iff_of_nonneg

end OrderedCommGroup

section CanonicallyOrderedCommMonoid

variable [CanonicallyOrderedCommMonoid α]

variable [TopologicalSpace α] [OrderClosedTopology α] {f : ι → α} {a : α}

@[to_additive]
theorem le_hasProd' (hf : HasProd f a) (i : ι) : f i ≤ a :=
  le_hasProd hf i fun _ _ => one_le _
#align le_has_prod' le_hasProd'
#align le_has_sum' le_hasSum'

@[to_additive le_tsum']
theorem le_tprod' (hf : Multipliable f) (i : ι) : f i ≤ ∏' i, f i :=
  le_tprod hf i fun _ _ => one_le _
#align le_tprod' le_tprod'
#align le_tsum' le_tsum'

@[to_additive]
theorem hasProd_one_iff : HasProd f 1 ↔ ∀ x, f x = 1 := by
  refine' ⟨_, fun h => _⟩
  · contrapose!
    exact fun ⟨x, hx⟩ h => hx (le_one_iff_eq_one.1 <| le_hasProd' h x)
  · convert @hasProd_one α ι _ _
    exact h _
#align has_prod_one_iff hasProd_one_iff
#align has_sum_zero_iff hasSum_zero_iff

@[to_additive tsum_eq_one_iff]
theorem tprod_eq_one_iff (hf : Multipliable f) : ∏' i, f i = 1 ↔ ∀ x, f x = 1 := by
  rw [← hasProd_one_iff, hf.hasProd_iff]
#align tprod_eq_one_iff tprod_eq_one_iff
#align tsum_eq_one_iff tsum_eq_one_iff

@[to_additive tsum_ne_zero_iff]
theorem tprod_ne_one_iff (hf : Multipliable f) : ∏' i, f i ≠ 1 ↔ ∃ x, f x ≠ 1 := by
  rw [Ne.def, tprod_eq_one_iff hf, not_forall]
#align tprod_ne_one_iff tprod_ne_one_iff
#align tsum_ne_zero_iff tsum_ne_zero_iff

@[to_additive isLUB_hasSum']
theorem isLUB_has_prod' (hf : HasProd f a) : IsLUB (Set.range fun s => ∏ i in s, f i) a :=
  isLUB_of_tendsto_atTop (Finset.prod_mono_set' f) hf
#align is_lub_has_prod' isLUB_has_prod'
#align is_lub_has_sum' isLUB_hasSum'

end CanonicallyOrderedCommMonoid

section LinearOrder

/-!
For infinite prods taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite prods is a criterion for prodmability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

@[to_additive]
theorem hasProd_of_isLUB_of_one_le [LinearOrderedCommMonoid α] [TopologicalSpace α]
    [OrderTopology α] {f : ι → α} (i : α) (h : ∀ i, 1 ≤ f i)
    (hf : IsLUB (Set.range fun s => ∏ i in s, f i) i) : HasProd f i :=
  tendsto_atTop_isLUB (Finset.prod_mono_set_of_one_le' h) hf
#align has_prod_of_is_lub_of_one_le hasProd_of_isLUB_of_one_le
#align has_sum_of_is_lub_of_nonneg hasSum_of_isLUB_of_nonneg

@[to_additive]
theorem hasProd_of_isLUB [CanonicallyLinearOrderedCommMonoid α] [TopologicalSpace α] [OrderTopology α]
    {f : ι → α} (b : α) (hf : IsLUB (Set.range fun s => ∏ i in s, f i) b) : HasProd f b :=
  tendsto_atTop_isLUB (Finset.prod_mono_set' f) hf
#align has_prod_of_is_lub hasProd_of_isLUB
#align has_sum_of_is_lub hasSum_of_isLUB

-- No has_abs.abs in the mul case
theorem summable_abs_iff [LinearOrderedAddCommGroup α] [UniformSpace α] [UniformAddGroup α]
    [CompleteSpace α] {f : ι → α} : (Summable fun x => |f x|) ↔ Summable f :=
  let s := { x | 0 ≤ f x }
  have h1 : ∀ x : s, |f x| = f x := fun x => abs_of_nonneg x.2
  have h2 : ∀ x : ↑sᶜ, |f x| = -f x := fun x => abs_of_neg (not_le.1 x.2)
  calc (Summable fun x => |f x|) ↔
      (Summable fun x : s => |f x|) ∧ Summable fun x : ↑sᶜ => |f x| :=
        summable_subtype_and_compl.symm
  _ ↔ (Summable fun x : s => f x) ∧ Summable fun x : ↑sᶜ => -f x := by simp only [h1, h2]
  _ ↔ Summable f := by simp only [summable_neg_iff, summable_subtype_and_compl]
#align summable_abs_iff summable_abs_iff


alias ⟨Summable.of_abs, Summable.abs⟩ := summable_abs_iff
#align summable.of_abs Summable.of_abs
#align summable.abs Summable.abs

theorem Finite.of_summable_const [LinearOrderedAddCommGroup α] [TopologicalSpace α] [Archimedean α]
    [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι => b) :
    Finite ι := by
  have H : ∀ s : Finset ι, s.card • b ≤ ∑' _ : ι, b := fun s => by
    simpa using sum_le_hasSum s (fun a _ => hb.le) hf.hasSum
  obtain ⟨n, hn⟩ := Archimedean.arch (∑' _ : ι, b) hb
  have : ∀ s : Finset ι, s.card ≤ n := fun s => by
    simpa [nsmul_le_nsmul_iff_left hb] using (H s).trans hn
  have : Fintype ι := fintypeOfFinsetCardLe n this
  infer_instance
theorem Set.Finite.of_summable_const [LinearOrderedAddCommGroup α] [TopologicalSpace α]
    [Archimedean α] [OrderClosedTopology α] {b : α} (hb : 0 < b) (hf : Summable fun _ : ι => b) :
    (Set.univ : Set ι).Finite :=
  finite_univ_iff.2 <| .of_summable_const hb hf
#align finite_of_summable_const Set.Finite.of_summable_const

end LinearOrder

theorem Summable.tendsto_atTop_of_pos [LinearOrderedField α] [TopologicalSpace α] [OrderTopology α]
    {f : ℕ → α} (hf : Summable f⁻¹) (hf' : ∀ n, 0 < f n) : Tendsto f atTop atTop :=
  inv_inv f ▸ Filter.Tendsto.inv_tendsto_zero <|
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hf.tendsto_atTop_zero <|
      eventually_of_forall fun _ => inv_pos.2 (hf' _)
#align summable.tendsto_top_of_pos Summable.tendsto_atTop_of_pos
