/- antidiagonal with values in more general types 
 inspired by a file of Bhavik Mehta 
! This file was ported from Lean 3 source module antidiagonal
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Interval
import Mathlib.RingTheory.PowerSeries.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Order

open scoped BigOperators

open Finset Function

variable {μ : Type _} [CanonicallyOrderedAddMonoid μ] [LocallyFiniteOrder μ] [DecidableEq μ]

variable {ι : Type _} [DecidableEq ι] [DecidableEq (ι → μ)]

variable {σ : Type _} [DecidableEq σ] [DecidableEq (ι → σ →₀ ℕ)]

variable {α : Type _} [CommSemiring α]

namespace Finset

#check Finsupp
/- We may wish to redefine : 

def Finsupp.antidiagonal (n : μ) : Set (ι →₀ μ) := sorry

so that it is valid in this generality

maybe not

-- almost as cut except the type
Finsupp.antidiagonal_with_support (s : Finset ι) (n : μ) : Finset (ι →₀ μ) := sorry

--  do not rewrite Multiset.antidiagonal using general antidiagonal with μ := Multiset α
Note that Multiset α ≃ (α →₀ ℕ),  s  ↦  (a ↦ s.count a), so it is a canonically ordered add monoid, with locally finite order
but we get different stuff

def s : Multiset ℕ := {0, 0, 0}

#eval (Finset.antidiagonal s).card
-- 4

#eval Multiset.card (Multiset.antidiagonal s)
-- 8

-- List.Nat.antidiagonal
returns a list and not only a finset
does not need to be rewritten (cool!)

-- Multiset.Nat.antidiagonal is defined using List.Nat.antidiagonal

-- Finset.Nat.antidiagonal is defined using Multiset.Nat.antidiagonal
maybe do not rewrite, but prove that it coincides


  
-/
#check Finset.Nat.antidiagonal
-- rename cut as Pi.antidiagonal
/-- The Finset of functions `ι → μ` whose support is contained in `s`
  and whose sum is `n` -/
def cut (s : Finset ι) (n : μ) : Finset (ι → μ) := --TODO: rename Pi.antidiagonal
  Finset.filter (fun f => s.sum f = n)
    ((s.pi fun _ => Iic n).map
      ⟨fun f i => if h : i ∈ s then f i h else 0, 
        fun f g h => by ext i hi; simpa only [dif_pos hi] using congr_fun h i⟩)
#align finset.cut Finset.cut

/-- For `n: μ`, the set of all finitely supported functions `ι →₀ μ` with sum `n`-/
def cut₀ (n : μ) : Set (ι →₀ μ) := { f | f.sum (fun _ x ↦ x) = n }


/-- The Finset of pairs of elements of `μ` with sum `n` -/
def antidiagonal (n : μ) : Finset (μ × μ) :=
  Finset.filter (fun uv => uv.fst + uv.snd = n) (Finset.product (Iic n) (Iic n))
#align finset.antidiagonal Finset.antidiagonal


@[simp]
theorem mem_antidiagonal (n : μ) (a : μ × μ) : a ∈ antidiagonal n ↔ a.fst + a.snd = n := by
  simp only [antidiagonal, Prod.forall, mem_filter, and_iff_right_iff_imp]
  intro h; rw [← h]
  erw [mem_product, mem_Iic, mem_Iic]
  exact ⟨le_self_add, le_add_self⟩
#align finset.mem_antidiagonal Finset.mem_antidiagonal

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: 
  expanding binder collection (i «expr ∉ » s) -/
@[simp]
theorem mem_cut (s : Finset ι) (n : μ) (f : ι → μ) :
    f ∈ cut s n ↔ s.sum f = n ∧ ∀ (i) (_ : i ∉ s), f i = 0 := by
  rw [cut, mem_filter, and_comm, and_congr_right]
  intro h
  simp only [mem_map, exists_prop, Function.Embedding.coeFn_mk, mem_pi]
  constructor
  · rintro ⟨_, _, rfl⟩ _ hi
    dsimp only
    rw [dif_neg hi]
  · intro hf
    refine' ⟨fun i _ => f i, fun i hi => _, _⟩
    · rw [mem_Iic, ← h]
      apply single_le_sum _ hi
      simp
    · ext x
      dsimp only
      rw [dite_eq_ite, ite_eq_left_iff, eq_comm]
      exact hf x
#align finset.mem_cut Finset.mem_cut

theorem cut_equiv_antidiagonal (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (cut univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk, ←
    Equiv.eq_symm_apply]
  simp [mem_cut, add_comm, mem_antidiagonal]
#align finset.cut_equiv_antidiagonal Finset.cut_equiv_antidiagonal

theorem cut_zero (s : Finset ι) : cut s (0 : μ) = {0} := by
  ext f
  rw [mem_cut, mem_singleton, sum_eq_zero_iff, ← forall_and, funext_iff]
  apply forall_congr'
  intro i
  simp only [← or_imp, em (i ∈ s), forall_true_left, Pi.zero_apply]
#align finset.cut_zero Finset.cut_zero

theorem cut_empty (n : μ) : cut (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  ext f
  rw [mem_cut]
  simp only [sum_empty, not_mem_empty, not_false_iff, forall_true_left]
  split_ifs with hn
  simp only [hn, mem_singleton, funext_iff, eq_self_iff_true, true_and_iff, Pi.zero_apply]
  simp only [not_mem_empty, iff_false_iff]
  intro h'; exact hn h'.1.symm
#align finset.cut_empty Finset.cut_empty

theorem cut_insert (n : μ) (a : ι) (s : Finset ι) (h : a ∉ s) :
    cut (insert a s) n =
      (antidiagonal n).biUnion fun p : μ × μ =>
        (cut s p.snd).image fun f => Function.update f a p.fst := by
  ext f
  rw [mem_cut, mem_biUnion, sum_insert h]
  constructor
  · rintro ⟨rfl, h₁⟩
    simp only [exists_prop, Function.Embedding.coeFn_mk, mem_map, mem_antidiagonal, Prod.exists]
    use f a, s.sum f
    constructor; rfl
    rw [mem_image]
    use Function.update f a 0
    constructor
    · rw [mem_cut s (s.sum f)]
      constructor
      apply Finset.sum_congr rfl
      intro i hi; rw [Function.update_apply]; rw [if_neg]; intro hia; apply h; rw [← hia]; exact hi
      intro i hi; rw [Function.update_apply]; split_ifs with hia
      rfl
      apply h₁; simp only [mem_insert, not_or]; exact ⟨hia, hi⟩
    · ext i
      rw [Function.update_apply (update f a 0), Function.update_apply]
      split_ifs with hia
      rw [hia]
      rfl
  · simp only [mem_insert, mem_antidiagonal, mem_image, exists_prop, Prod.exists,
      forall_exists_index, and_imp, mem_cut]
    rintro d e rfl g hg hg' rfl
    constructor
    · simp only [Function.update_same]
      apply congr_arg₂ _ rfl
      rw [← hg]
      apply Finset.sum_congr rfl
      intro i hi; rw [Function.update_noteq _]
      intro hia; apply h; simpa only [hia] using hi
    · intro i hi; rw [not_or] at hi 
      rw [Function.update_noteq hi.1]
      exact hg' i hi.2
#align finset.cut_insert Finset.cut_insert

end Finset

theorem Finsupp.antidiagonal_eq_antidiagonal (d : σ →₀ ℕ) : 
    d.antidiagonal = Finset.antidiagonal d := by
  ext x
  rw [Finsupp.mem_antidiagonal, Finset.mem_antidiagonal]
#align finsupp.antidiagonal_eq_antidiagonal Finsupp.antidiagonal_eq_antidiagonal

example (n : ℕ) : Finset.Nat.antidiagonal n = Finset.antidiagonal n := by
    ext ⟨p,q⟩
    simp only [Nat.mem_antidiagonal, Finset.mem_antidiagonal]

example (α : Type*) [DecidableEq α] (s p q: Multiset α) :
    ⟨p, q⟩ ∈ Finset.antidiagonal s ↔
      ⟨p, q⟩ ∈ s.antidiagonal := by 
  simp only [Multiset.mem_antidiagonal, Finset.mem_antidiagonal]


#exit

-- TODO : move elsewhere
namespace MvPowerSeries

open Finset

/-- The `d`th coefficient of a finite product over `s` of power series 
is the sum of products of coefficients indexed by `cut s d` -/
theorem coeff_prod (s : Finset ι) (f : ι → MvPowerSeries σ α) (d : σ →₀ ℕ) :
    coeff α d (∏ j in s, f j) = ∑ l in cut s d, ∏ i in s, coeff α (l i) (f i) := by
  revert d
  refine' Finset.induction_on s _ _
  · intro d
    simp only [prod_empty, cut_empty, coeff_one]
    split_ifs <;> simp
  . intro a s ha ih d
    rw [cut_insert _ _ _ ha, prod_insert ha, coeff_mul, sum_biUnion]
    . apply Finset.sum_congr (Finsupp.antidiagonal_eq_antidiagonal d)
      rintro ⟨u, v⟩ huv
      simp only [mem_antidiagonal] at huv 
      dsimp
      rw [sum_image _]
      simp only [Pi.add_apply, Function.Embedding.coeFn_mk, prod_insert ha, if_pos rfl, ih, mul_sum]
      apply sum_congr rfl
      · intro k _
        apply congr_arg₂ _
        rw [Function.update_same]
        apply Finset.prod_congr rfl
        intro i hi; rw [Function.update_noteq]
        intro hi'; apply ha; simpa [hi'] using hi
      · intro k hk l hl
        simp only [funext_iff]; apply forall_imp
        intro i h
        simp only [mem_cut] at hk hl 
        by_cases hi : i = a
        rw [hi, hk.2 a ha, hl.2 a ha]
        simpa only [Function.update_noteq hi] using h
    · simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, mem_antidiagonal]
      rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
      rw [onFun_apply, disjoint_left]
      intro k hk hl; simp only [mem_image] at hk hl 
      obtain ⟨k, hk, rfl⟩ := hk
      obtain ⟨l, hl, hkl⟩ := hl
      simp only [mem_cut] at hk hl 
      apply h; simp only [Prod.mk.inj_iff]
      suffices : u = u'
      apply And.intro this
      rw [this, ← huv'] at huv 
      simpa only [add_right_inj] using huv
      apply symm
      simpa only [Function.update_same] using funext_iff.mp hkl a
    --sorry
#align mv_power_series.coeff_prod MvPowerSeries.coeff_prod

variable [DecidableEq (ℕ → σ →₀ ℕ)]

/-- The `d`th coefficient of a finite product over `s` of power series 
is the sum of products of coefficients indexed by `cut s d` -/
theorem coeff_pow (f : MvPowerSeries σ α) (n : ℕ) (d : σ →₀ ℕ) :
    coeff α d (f ^ n) = ∑ l in cut (Finset.range n) d, ∏ i in Finset.range n, coeff α (l i) f :=
  by
  suffices : f ^ n = (Finset.range n).prod fun _ => f
  rw [this, coeff_prod]
  rw [Finset.prod_const, card_range]
#align mv_power_series.coeff_pow MvPowerSeries.coeff_pow

/-- Bourbaki, Algèbre, chap. 4, §4, n°2, proposition 3 -/
theorem coeff_eq_zero_of_constantCoeff_nilpotent (f : MvPowerSeries σ α) (m : ℕ)
    (hf : constantCoeff σ α f ^ m = 0) (d : σ →₀ ℕ) (n : ℕ) (hn : m + degree d ≤ n) :
    coeff α d (f ^ n) = 0 := by
  rw [coeff_pow]
  apply sum_eq_zero
  intro k hk
  rw [mem_cut] at hk 
  let s := (range n).filter fun i => k i = 0 
  suffices hs : s ⊆ range n
  . rw [← prod_sdiff hs]
    refine' mul_eq_zero_of_right _ _
    have hs' : ∀ i ∈ s, coeff α (k i) f = constantCoeff σ α f := by
      simp only [mem_filter]
      intro i hi
      rw [hi.2, coeff_zero_eq_constantCoeff]
    rw [prod_congr rfl hs', prod_const]
    suffices : m ≤ s.card
    . obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le this
      rw [hm', pow_add, hf, MulZeroClass.zero_mul]
    rw [← Nat.add_le_add_iff_right, add_comm s.card, Finset.card_sdiff_add_card_eq_card hs]
    simp only [card_range]
    apply le_trans _ hn
    simp only [add_comm m, Nat.add_le_add_iff_right]
    rw [← hk.1, map_sum, ← sum_sdiff hs]
    have hs'' : ∀ i ∈ s, degree (k i) = 0 := by 
      simp only [mem_filter]
      intro i hi
      rw [hi.2, map_zero]
    rw [sum_eq_zero hs'', add_zero]
    convert Finset.card_nsmul_le_sum (range n \ s) _ 1 _
    simp only [Algebra.id.smul_eq_mul, mul_one]
    · simp only [mem_filter, mem_sdiff, mem_range, not_and, and_imp]
      intro i hi hi'; rw [← not_lt]; intro h; apply hi' hi
      simpa only [Nat.lt_one_iff, degree_eq_zero_iff] using h
  apply filter_subset
#align mv_power_series.coeff_eq_zero_of_constant_coeff_nilpotent
  MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent

end MvPowerSeries

/-  This is a variant that produces finsupp functions. Is it useful?

noncomputable example (s : finset ι) (t : set ↥s) : finset ι :=
 s.filter (λ i, i ∈ (coe : ↥s → ι) '' t)
--  (s.attach.filter (λi, i ∈  t)).map (?subtype.coe)

noncomputable def finsupp_of {ι: Type*} {s : finset ι} (f : s → μ) : ι →₀ μ := {
to_fun := λ i, if h : i ∈ s then f ⟨i, h⟩ else 0,
support := s.filter (λ i, i ∈ (coe : ↥s → ι) '' f.support),
mem_support_to_fun := λ i,
begin
  simp only [set.mem_image, mem_support, ne.def, finset.exists_coe, subtype.coe_mk, 
    exists_and_distrib_right, exists_eq_right,
  mem_filter, dite_eq_right_iff, not_forall, and_iff_right_iff_imp, forall_exists_index],
  intros hx _, exact hx,
end }

/-- finsupp.cut s n is the finset of finitely supported functions with sum n
  whose support is contained in s -/
noncomputable def finsupp.cut {ι : Type*} (s : finset ι) (n : μ) : finset (ι →₀ μ) :=
finset.filter (λ f, f.sum (λ u v, v) = n) ((s.pi (λ _, Iic n)).map 
  ⟨λ f, ({
    to_fun := λ i, if h : i ∈ s then f i h else 0, 
    support := s.filter (λ i, ∃ h : i ∈ s, f i h ≠ 0),
    mem_support_to_fun := λ i, 
    begin
      simp only [ne.def, mem_filter, dite_eq_right_iff, not_forall, and_iff_right_iff_imp,
        forall_exists_index],
      intros hi _, exact hi,
    end } : ι →₀ μ), 
  λ f g h, 
  begin 
    ext i hi, 
    simp only [ne.def, filter_congr_decidable, funext_iff] at h,
    let hi' := h.2 i, 
    simpa only [dif_pos hi] using h.2 i,
  end ⟩)

lemma finsupp.mem_cut  {ι : Type*} (s : finset ι) (n : μ) (f : ι →₀ μ) :
  f ∈ finsupp.cut s n ↔ f.sum (λ u v, v) = n ∧ ∀ i ∉ s, f i = 0 :=
begin
  rw [finsupp.cut, mem_filter, and_comm, and_congr_right], 
  intro h,
  simp only [mem_map, exists_prop, function.embedding.coe_fn_mk, mem_pi],
  split,
  { rintro ⟨_, _, rfl⟩ _ _,
    simp [dif_neg H] },
  { intro hf,
    refine ⟨λ i hi, f i, λ i hi, _, _⟩,
    { rw [mem_Iic, ← h],
      suffices : f.support ⊆ s,
      rw f.sum_of_support_subset this,
      apply finset.single_le_sum _ hi,
      intros i hi, apply zero_le,
      simp,
      intros i, rw [finsupp.mem_support_iff, not_imp_comm], exact hf i, },
    { ext i,
      simp only [finsupp.coe_mk, dite_eq_ite, ite_eq_left_iff],
      intro hi, rw hf i hi, } }
end
 -/

--#lint