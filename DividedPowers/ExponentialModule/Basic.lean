/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowers.ForMathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Ring.Ext

/-! # Exponential module of a commutative ring

Let `R` be a commutative ring. The exponential module of `R` is the set of all power series
`f : R⟦X⟧` that are of exponential type : `f (X + Y) = f X * f Y` where `X` and `Y` are two
indeterminates. It is an abelian group under multiplication, and an `R`-module under rescaling.

## Main Definitions

* `PowerSeries.IsExponential` : for `f : R⟦X⟧`, `IsExponential f` says that `f` is of
  exponential type.

* `PowerSeries.ExponentialModule R` : the exponential module of the commutative ring `R`.

* `PowerSeries.ExponentialModule.linearMap`: for an `A`-algebra map `f : R →ₐ[A] S`, we define
  the induced `linearMap f : ExponentialModule R →ₗ[A] ExponentialModule S`.

## Main Results

* `PowerSeries.IsExponential.neg` : if `f : R⟦X⟧` is an exponential power series, then the power
  series `f(-X)` is exponential.

* `PowerSeries.IsExponential.invOfUnit_eq_rescale_neg_one` : if `f : R⟦X⟧`, then the inverse of `f`
  is equal to the power series `f(-X)`.

## TODO

Once substitution of power series is available for `CommSemiring` (work in progress),
`PowerSeries.IsExponential` and `PowerSeries.ExponentialModule R` could automatically be generalized
to that setting.

-/

section Preliminaries

-- In #30974 (Merged)
-- [Mathlib.Algebra.Algebra.Basic]
/- The `CommRing` structure on a `CommSemiring` induced by a ring morphism from a `CommRing`. -/
/- def RingHom.commSemiringToCommRing
    {R S : Type*} [CommRing R] [CommSemiring S] (φ : R →+* S) :
    CommRing S := by
  let _ : Algebra R S := RingHom.toAlgebra φ
  refine {
    toRing := Algebra.semiringToRing R
    mul_comm := CommMonoid.mul_comm } -/

section SMul

-- In #30972

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommSemiring R]

-- [Mathlib.RingTheory.MvPowerSeries.Basic]
/- @[simp]
lemma MvPolynomial.coe_smul (φ : MvPolynomial σ R) (r : R) :
  (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

-- [Mathlib.RingTheory.PowerSeries.Basic]
@[simp]
lemma Polynomial.coe_smul (φ : Polynomial R) (r : R) :
  (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl -/

end SMul

open Finset Finsupp MvPowerSeries Nat

section CommSemiring

variable {R : Type*} [CommSemiring R]

section

namespace Finsupp

-- In #30975, except for the last lemma

variable {σ α : Type*} [Zero α] (f g : σ → α) (s : Finset σ)
  [DecidablePred fun i ↦ i ∈ s] [DecidablePred fun i ↦ f i ≠ 0]

/- /-- The restriction of a finitely supported map `σ →₀ α` to `s : Finset σ`. -/
def restrict : σ →₀ α where
  toFun i := if i ∈ s then f i else 0
  support := {i ∈ s | f i ≠ 0}
  mem_support_toFun i := by simp -/

--noncomputable def restrict : σ →₀ α := Finsupp.indicator s (fun i _ ↦ f i)

/- lemma restrict_eq_restrict' {i : σ} :
    restrict f s i = restrict' f s i := by
  simp? [restrict, restrict', indicator] -/

variable {f g s}

/- theorem restrict_apply {i : σ} :
  restrict f s i = if i ∈ s then f i else 0 := by simp [restrict, indicator] -/

/- theorem restrict_support_le : (restrict f s).support ⊆ s := by
  rw [restrict]

  exact Finsupp.support_indicator_subset s (fun i x ↦ f i) -/
  /- simp only [mem_support_iff, restrict_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at hi
  exact hi.1 -/

theorem indicator_indicator (f' : (i : σ) → i ∈ s → α) [DecidableEq σ] {t : Finset σ}
    [DecidablePred fun i ↦ i ∈ t] [DecidablePred fun i ↦ i ∈ s ∩ t]
    [DecidablePred fun i ↦ (indicator s f') i ≠ 0] :
    indicator t (fun i _ ↦ indicator s f' i) =
      indicator (s ∩ t) (fun i hi ↦ f' i (Finset.mem_of_mem_inter_left hi)) := by
  ext i
  simp only [indicator_apply]
  by_cases ht : i ∈ t
  · rw [dif_pos ht]
    by_cases hs : i ∈ s
    · rw [dif_pos hs, dif_pos (mem_inter_of_mem hs ht)]
    · rw [dif_neg hs, dif_neg (fun hs' ↦ hs (Finset.inter_subset_left hs'))]
  · rw [dif_neg ht, dif_neg (fun ht' ↦ ht (Finset.inter_subset_right ht'))]


example (f' : (i : σ) → i ∈ s → α) : (∀ (i : σ), if hi : i ∈ s then f' i hi = g i else g i = 0) ↔
    ((∀ (i : σ) (hi : i ∈ s),  f' i hi = g i) ∧ ∀ i (_ : i ∉ s), g i = 0) := by
  grind

theorem eq_indicator_iff (f' : (i : σ) → i ∈ s → α) :
    g = indicator s f' ↔ g.support ⊆ s ∧ ∀ i (hi : i ∈ s), f' i hi = g i := by
  suffices g.support ⊆ s ∧ (∀ i (hi : i ∈ s), f' i hi = g i) ↔
      (∀ i , if hi : i ∈ s then f' i hi = g i else g i = 0) by
    rw [this, funext_iff]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;>
    simp only [indicator, ne_eq, univ_eq_attach, coe_mk, hi, ↓reduceDIte]
    rw [eq_comm]
  rw [Set.subset_def, and_comm]
  have : (∀ (i : σ), if hi : i ∈ s then f' i hi = g i else g i = 0) ↔
      ((∀ (i : σ) (hi : i ∈ s),  f' i hi = g i) ∧ ∀ i (hi : i ∉ s), g i = 0) := by
    grind
  rw [this]
  apply and_congr
  · rfl
  · simp [not_imp_comm]

/- theorem self_eq_restrict_iff (f : (i : σ) → i ∈ s → α)  :
  fun i ↦ f i _ = indicator s f ↔ f.support ⊆ s := by
  sorry -/

-- In #30976 (Merged)
--[Mathlib.Data.Nat.Choose.Multinomial]
/- theorem multinomial_eq_of_support_subset
    {α : Type*} {f : α →₀ ℕ} {s : Finset α} (h : f.support ⊆ s) :
    f.multinomial = Nat.multinomial s f := by
  simp only [Finsupp.multinomial_eq, Nat.multinomial]
  congr 1
  · simp [Finset.sum_subset h]
  · rw [Finset.prod_subset h]
    intro x _
    simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not, factorial_eq_one]
    grind -/

end Finsupp

end

namespace MvPolynomial

-- PR this section [Mathlib.Algebra.MvPolynomial.Basic], if possible

theorem prod_X_pow {σ : Type*} [DecidableEq σ] (x : σ → ℕ) (s : Finset σ) :
    ∏ y ∈ s, (X y : MvPolynomial σ R) ^ x y =
      monomial (Finsupp.indicator s (fun i _ ↦ x i)) (1 : R) := by
  rw [monomial_eq, C_1, one_mul, prod,
    Finset.prod_subset (s₁ := (Finsupp.indicator s (fun i _ ↦ x i)).support) (s₂ := s)
      (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi ↦ by simp [Finsupp.indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff, ne_eq, not_not] at hi'
    rw [hi', pow_zero]

theorem coeff_prod_X_pow {σ : Type*} [DecidableEq σ] (s : Finset σ) (d : σ →₀ ℕ) (x : σ → ℕ)
    [DecidablePred fun i ↦ i ∈ s] [Decidable (d = Finsupp.indicator s (fun i _ ↦ x i))] :
    coeff d (∏ y ∈ s, (X y : MvPolynomial σ R) ^ x y) =
      if d = Finsupp.indicator s (fun i _ ↦ x i) then 1 else 0 := by
  rw [prod_X_pow x s, coeff_monomial]
  simp_rw [eq_comm]

private theorem coeff_linearCombination_X_pow_of_eq {σ : Type*} (a : σ →₀ R) {d : σ →₀ ℕ} {n : ℕ}
    (hd : d.sum (fun _ m ↦ m) = n) :
    coeff d (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      d.multinomial * d.prod (fun r m ↦ a r ^ m) := by
  classical
  simp only [Finsupp.sum, Finsupp.linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag,
    coeff_sum]
  simp_rw [← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_C_mul, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Finsupp.indicator a.support (fun i _ ↦ d i) : σ → ℕ)]
  · simp only [← DFunLike.coe_fn_eq, Finsupp.indicator_indicator]
    split_ifs with hd'
    swap
    · simp [funext_iff] at hd'
      obtain ⟨i, hi, hdi⟩ := hd'
      rw [eq_comm]
      convert mul_zero _
      rw [← d.mul_prod_erase i, hi, zero_pow hdi, zero_mul]
      exact Finsupp.mem_support_iff.mpr hdi
    replace hd' : ∀ i, a i = 0 → d i = 0 := by
      simpa [funext_iff] using hd'
    have hd'' : d.support ⊆ a.support := fun i hi ↦ by
      simp [Finsupp.mem_support_iff] at hi ⊢
      exact fun h ↦ hi (hd' i h)
    rw [← Finset.prod_sdiff hd'', ← mul_assoc, Finsupp.prod]
    apply congr_arg₂
    · convert mul_one _
      · apply Finset.prod_eq_one
        intro i hi
        simp only [mem_sdiff, Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hi
        simp [hi.2, hi]
      · sorry
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [indicator_apply, Finsupp.mem_support_iff, ne_eq, dite_eq_ite, ite_not, pow_ite,
        pow_zero, ite_eq_right_iff]
      intro hi'
      suffices d i = 0 by simp [this]
      exact hd' i hi'

/-

    simp only [inter_self,
      Finsupp.self_eq_restrict_iff, fun_support_eq, coe_subset]
    split_ifs with hd'
    · have : d = Finsupp.restrict d a.support := by
        simp [← DFunLike.coe_fn_eq, Finsupp.self_eq_restrict_iff, hd']
      rw [← this]
      congr 1
      · rw [Finsupp.multinomial_eq_of_support_subset hd']
      · rw [Finsupp.prod, Finset.prod_subset hd']
        intro x _ hx
        simp only [Finsupp.mem_support_iff, ne_eq, not_not] at hx
        rw [hx, pow_zero]
    · symm
      convert mul_zero _
      obtain ⟨x, hx, hx'⟩ := not_subset.mp hd'
      apply Finset.prod_eq_zero hx
      simp only [Finsupp.mem_support_iff, ne_eq, Decidable.not_not] at hx hx'
      simp [hx', zero_pow hx]
  · intro x hx hx'
    rw [if_neg]
    intro hd
    apply hx'
    rw [Finsupp.eq_restrict_iff, hd]
    exact ⟨(mem_piAntidiag.mp hx).2, fun _ hi ↦ by rw [Finsupp.restrict_apply, if_pos hi]⟩
  · intro hd'
    rw [if_neg]
    intro hd''
    apply hd'
    simp only [mem_piAntidiag, ne_eq]
    constructor
    · rw [← hd, Finsupp.sum, Finset.sum_subset (s₁ := d.support) (s₂ := a.support)
        ((Finsupp.ext_iff'.mp hd'').1 ▸ Finsupp.restrict_support_le) (fun _ ↦ by simp)]
      exact Finset.sum_congr rfl (fun _ hx ↦ by rw [Finsupp.restrict_apply, if_pos hx])
    · intro i hi
      simp only [restrict_apply, Finsupp.mem_support_iff, ne_eq, ite_not, ite_eq_left_iff,
        Classical.not_imp] at hi ⊢
      exact hi.1
-/

private theorem coeff_linearCombination_X_pow_of_ne {σ : Type*} (a : σ →₀ R) {d : σ →₀ ℕ} {n : ℕ}
    (hd : d.sum (fun _ m ↦ m) ≠ n) :
    coeff d (((a.linearCombination R X : MvPolynomial σ R)) ^ n) = 0 := by
  classical
  simp only [Finsupp.sum, Finsupp.linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag,
    coeff_sum]
  simp_rw [← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_C_mul, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero
  intro x hx
  rw [if_neg]
  rintro ⟨rfl⟩
  apply hd
  sorry --TODO
  /- rw [Finsupp.sum, ← (mem_piAntidiag.mp hx).1,
    Finset.sum_subset (Finsupp.restrict_support_le) (fun _ _ ↦ by simp)]
  exact Finset.sum_congr rfl (fun _ hi ↦ by rw [Finsupp.restrict_apply, if_pos hi]) -/

theorem coeff_linearCombination_X_pow {σ : Type*} (a : σ →₀ R) (d : σ →₀ ℕ) (n : ℕ) :
    coeff d (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m ↦ m) = n then d.multinomial * d.prod (fun r m ↦ a r ^ m) else 0 := by
  split_ifs with hd
  · exact coeff_linearCombination_X_pow_of_eq a hd
  · exact coeff_linearCombination_X_pow_of_ne a hd

theorem coeff_linearCombination_X_pow_of_fintype
    {σ : Type*} [Fintype σ] (a : σ → R) (d : σ →₀ ℕ) (n : ℕ) :
    coeff d (((∑ i, a i • X i : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m ↦ m) = n then d.multinomial * d.prod (fun r m ↦ a r ^ m) else 0 := by
  rw [← Finsupp.ofSupportFinite_coe (f := a) (hf := Set.toFinite _),
    Finsupp.prod_congr (fun r _ ↦ rfl), ← coeff_linearCombination_X_pow]
  simp [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset (s := univ)]

theorem coeff_sum_X_pow_of_fintype {σ : Type*} [Fintype σ] (d : σ →₀ ℕ) (n : ℕ) :
    coeff d (((∑ i, X i : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m ↦ m) = n then d.multinomial else 0 := by
  let a : σ → R := Function.const _ 1
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, a i • X i := by simp [a]
  rw [this, coeff_linearCombination_X_pow_of_fintype]
  simp only [Function.const_one, Pi.one_apply, one_pow, cast_ite, cast_zero, a]
  split_ifs with hi
  · convert mul_one _
    exact Finset.prod_eq_one (by simp)
  · rfl

/-- The formula for the `d`th coefficient of `(X 0 + X 1) ^ n`. -/
lemma coeff_add_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    coeff d ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) =
      if (d 0, d 1) ∈ antidiagonal n then n.choose (d 0) else 0 := by
  rw [← Fin.sum_univ_two, coeff_sum_X_pow_of_fintype]
  congr 1
  have : d.sum (fun x m ↦ m) = d 0 + d 1 := by
    simp [Finsupp.sum_of_support_subset d (subset_univ d.support)]
  simp only [mem_antidiagonal, this]
  split_ifs with hd
  · rw [Finsupp.multinomial_eq_of_support_subset (subset_univ d.support)]
    erw [Nat.binomial_eq_choose Fin.zero_ne_one]
    simp [hd]
  · rfl

end MvPolynomial

end CommSemiring

namespace PowerSeries

variable {A R S : Type*}

section Bivariate

section CommSemiring

variable [CommSemiring A] [CommSemiring R] [Algebra A R] [CommSemiring S] [Algebra A S]

/-- Notation for the first variable of the bivariate power series ring `R⟦X₀, X₁⟧. -/
noncomputable abbrev X₀ {R : Type*} [Semiring R] := MvPowerSeries.X (σ := Fin 2) (R := R) 0

/-- Notation for the second variable of the bivariate power series ring `R⟦X₀, X₁⟧. -/
noncomputable abbrev X₁ {R : Type*} [Semiring R] := MvPowerSeries.X (σ := Fin 2) (R := R) 1

lemma forall_congr_curry {α : Type*} {p : (Fin 2 → α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 → α, p e ↔ q (e 0) (e 1)) :
    (∀ (e : Fin 2 → α), p e) ↔ ∀ (u v : α), q u v := by
  rw [Equiv.forall_congr_left (finTwoArrowEquiv α)]
  simp only [finTwoArrowEquiv_symm_apply, Prod.forall, hpq]
  rfl

lemma forall_congr_curry₀ {α : Type*} [Zero α] {p : (Fin 2 →₀ α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 →₀ α, p e ↔ q (e 0) (e 1)) :
    (∀ e, p e) ↔ ∀ u v, q u v := by
  rw [Equiv.forall_congr_left (equivFunOnFinite.trans (finTwoArrowEquiv α))]
  simp [finTwoArrowEquiv_symm_apply, Prod.forall, hpq]

end CommSemiring

section CommRing

variable [CommRing R]

lemma coeff_subst_single {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (subst (MvPowerSeries.X s) f) =
      if e = single s (e s) then PowerSeries.coeff (e s) f else 0 := by
  rw [PowerSeries.coeff_subst (HasSubst.X s), finsum_eq_single _ (e s)]
  · rw [MvPowerSeries.coeff_X_pow, smul_eq_mul]
    split_ifs with he
    · rw [mul_one]
    · rw [mul_zero]
  · intro d hd
    simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro hd'
    simp [hd'] at hd

lemma coeff_subst_add_X₀_X₁ (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff e) (subst (X₀ + X₁) f) =
      (e 0 + e 1).choose (e 0) * coeff (e 0 + e 1) f := by
  rw [PowerSeries.subst, MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ ↦ by simp))]
  simp only [Fin.isValue, Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul]
  simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
    MvPolynomial.coeff_coe]
  rw [finsum_eq_single _ (single () (e 0 + e 1)), mul_comm]
  · apply congr_arg₂
    simp only [Fin.isValue, single_add, Finsupp.coe_add, Pi.add_apply, single_eq_same,
      MvPolynomial.coeff_add_pow, mem_antidiagonal, reduceIte]
    simp [coeff]
  · intro d hd'
    simp only [Fin.isValue, MvPolynomial.coeff_add_pow, mem_antidiagonal, cast_ite, cast_zero,
      mul_ite, mul_zero, ite_eq_right_iff]
    intro hd
    have hd_eq : d = single () (e 0 + e 1) := by ext; simp [hd]
    exact absurd hd_eq hd'

lemma coeff_subst_mul_X₀_X₁ (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (subst X₀ f * subst X₁ f) = coeff (e 0) f * coeff (e 1) f := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (single 0 (e 0), single 1 (e 1)) ?_ ?_]
  · apply congr_arg₂ <;> simp [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← mem_antidiagonal.mp hb, h0.1, h1.1]
    simp
  · intro he
    have he' : single 0 (e 0) + single 1 (e 1) = e := by
      ext i
      match i with
      | 0 => simp
      | 1 => simp
    exact absurd (mem_antidiagonal.mpr he') he

end CommRing

end Bivariate

section CommSemiring

-- TODO: generalize to `CommSemiring R`.
variable [CommSemiring A] [CommRing R] [Algebra A R] [CommSemiring S] [Algebra A S]

/-- A power series `f : R⟦X⟧` is exponential if `f(X + Y) = f(X)*f(Y)` and `f(0) = 1`. -/
structure IsExponential (f : R⟦X⟧) : Prop where
  add_mul : subst (S := R) (X₀ + X₁) f = subst X₀ f * subst X₁ f
  constantCoeff : constantCoeff f = 1

/-- A power series `f` satisfies `f(X + Y) = f(X)*f(Y)` iff its coefficients `f n` satisfy
  the relations `(p + q).choose p * f (p + q)= f p * f q`. -/
theorem subst_add_eq_mul_iff {R : Type*} [CommRing R] (f : R⟦X⟧) :
    (subst (S := R) (X₀ + X₁) f) = (subst X₀ f) * (subst X₁ f) ↔
      ∀ (p q : ℕ), (p + q).choose p * (coeff (p + q) f) = coeff p f * coeff q f := by
  rw [MvPowerSeries.ext_iff]
  exact forall_congr_curry₀ (fun e ↦ by rw [coeff_subst_add_X₀_X₁ , coeff_subst_mul_X₀_X₁])

/-- A power series `f` is exponential iff its coefficients `f n` satisfy the relations
  `(p + q).choose p * f (p + q)= f p * f q` and its constant coefficient is `1`. -/
theorem isExponential_iff {f : R⟦X⟧} :
    IsExponential f ↔ (∀ p q, (p + q).choose p * coeff (p + q) f = coeff p f * coeff q f) ∧
      (constantCoeff f = 1) := by
  rw [← subst_add_eq_mul_iff]
  exact ⟨fun hf ↦ ⟨hf.add_mul, hf.constantCoeff⟩, fun hf ↦ ⟨hf.1, hf.2⟩⟩

namespace IsExponential

/-- The unit power series is exponential -/
protected theorem one : IsExponential (1 : R⟦X⟧) where
  add_mul := by
    rw [← Polynomial.coe_one, subst_coe (HasSubst.X 1), subst_coe (HasSubst.X 0),
      subst_coe ((HasSubst.X 0).add (HasSubst.X 1))]
    simp
  constantCoeff := by simp only [map_one]

/-- If `f` and `g` are exponential, then so is `f * g`. -/
protected theorem mul {f g : PowerSeries R} (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) where
  add_mul := by
    repeat rw [← coe_substAlgHom (HasSubst.of_constantCoeff_zero (by simp))]
    simp only [map_mul, coe_substAlgHom, hf.add_mul, hg.add_mul]
    ring
  constantCoeff := by simp only [map_mul, hf.constantCoeff, hg.constantCoeff, mul_one]

/-- If `f` is exponential and  `n : ℕ`, then `f ^ n` is exponential. -/
protected theorem npow {f : R⟦X⟧} (hf : IsExponential f) (n : ℕ) :
    IsExponential (f ^ n) := by
  induction n with
  | zero => simp [pow_zero, IsExponential.one]
  | succ n hn => simp [pow_succ, hn.mul hf]

/-- If `f` is exponential, then `f(r • T)` is exponential, for any `r : R`. -/
protected theorem rescale (a : A) {f : PowerSeries R} (hf : IsExponential f) :
    IsExponential (rescale (algebraMap A R a) f) := by
  rw [isExponential_iff] at hf ⊢
  refine ⟨fun p q ↦ ?_, ?_⟩
  · simp only [coeff_rescale, mul_mul_mul_comm, ← hf.1 p q]
    ring
  · rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp [hf.2]

/- /-- A version of `Commute.add_pow` that avoids ℕ-subtraction by summing over the antidiagonal and
also with the binomial coefficient applied via scalar action of ℕ. -/
theorem add_pow' (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2) := by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ fun m p ↦ n.choose m • (x ^ m * y ^ p),
    nsmul_eq_mul, cast_comm, h.add_pow]

end Commute -/

/-- The **binomial theorem** -/
theorem _root_.add_pow' (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2) :=
  (Commute.all x y).add_pow' n

protected theorem rescale_add (r s : A) {f : R⟦X⟧} (hf : IsExponential f) :
    rescale (algebraMap A R r + algebraMap A R s) f =
      rescale (algebraMap A R r) f * rescale (algebraMap A R s) f := by
  rw [isExponential_iff] at hf
  ext d
  simp only [coeff_rescale, coeff_mul, add_pow', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mem_antidiagonal.mp hk, nsmul_eq_mul, mul_assoc, mul_comm _ ((coeff (k.1 + k.2)) f),
    ← mul_assoc, hf.1 k.1 k.2]
  ring

end IsExponential

open Additive

section Instances

noncomputable instance : SMul A (Additive R⟦X⟧) where
  smul r f := ofMul.toFun (rescale (algebraMap A R r) (toMul f))

lemma toAdditive_smul_coe (r : A) (f : R⟦X⟧) :
  r • (ofMul f) = ofMul (rescale (algebraMap A R r) f) := rfl

lemma toAdditive_smul_coe' (r : A) (f : Additive R⟦X⟧) :
  toMul (r • f) = rescale (algebraMap A R r) (toMul f) := rfl

noncomputable instance : DistribMulAction A (Additive R⟦X⟧) where
  one_smul := by simp [toAdditive_smul_coe]
  mul_smul := by
    suffices  ∀ (x y : A) (b : Additive R⟦X⟧), (y * x) • b = x • y • b by
      intro x y b
      rw [← this, mul_comm]
    simp [toAdditive_smul_coe, rescale_mul]
  smul_zero a := by
    rw [← ofMul_one, toAdditive_smul_coe, map_one]
  smul_add := by simp [toAdditive_smul_coe, ← ofMul_mul]

end Instances

variable (R) in
/-- The `R`-module of exponential power series `f : R⟦X⟧` satisfying `f(X+Y) = f(X) f(Y)` and
  `f(0) = 1`. The addition law is the multiplication of power series.
  The scalar multiplication law is given by `PowerSeries.rescale`.
  This is implemented as an `AddSubmonoid (Additive R⟦X⟧) `. -/
def ExponentialModule : AddSubmonoid (Additive R⟦X⟧) where
  carrier := { f : Additive R⟦X⟧ | IsExponential (toMul f) }
  add_mem' {f g} hf hg := by simp [hf.mul hg]
  zero_mem' := by simp [IsExponential.one]

lemma mem_exponentialModule_iff (f : R⟦X⟧) :
    ofMul f ∈ ExponentialModule R ↔ IsExponential f := by
  simp [ExponentialModule]

lemma mem_exponentialModule_iff' (f : Additive R⟦X⟧) :
    f ∈ ExponentialModule R ↔ IsExponential (toMul f) := by
  simp [ExponentialModule]

namespace ExponentialModule

open PowerSeries Additive

/-- The coercion map from `ExponentialModule R` to `R⟦X⟧`. -/
@[coe] def toPowerSeries (f : ExponentialModule R) : R⟦X⟧ := toMul (f : Additive R⟦X⟧)

variable (R) in
instance instCoe : Coe (ExponentialModule R) R⟦X⟧ := ⟨toPowerSeries⟩

lemma coe_injective : Function.Injective ((↑) : ExponentialModule R → R⟦X⟧) :=
  fun f g ↦ by simp [toPowerSeries]

@[simp, norm_cast]
lemma coe_inj {f g : ExponentialModule R} : (f : R⟦X⟧) = ↑g ↔ f = g := coe_injective.eq_iff

@[ext]
lemma coe_ext {f g : ExponentialModule R} (h : (f : R⟦X⟧) = ↑g) : f = g := coe_injective h

@[simp]
theorem toMul_val_eq_coe {f : ExponentialModule R} : toMul (↑f : Additive R⟦X⟧) = ↑f := rfl

@[simp]
theorem coe_mk {f : R⟦X⟧} (hf : IsExponential f) : ↑(⟨ofMul f, hf⟩ : ExponentialModule R) = f := rfl

noncomputable instance instSMul : SMul A (ExponentialModule R) where
  smul r f := ⟨r • (f : Additive R⟦X⟧), by
    simp only [mem_exponentialModule_iff', toAdditive_smul_coe']
    exact f.prop.rescale (algebraMap A R r)⟩

theorem smul_def (r : A) (f : ExponentialModule R) :
  (r • f : ExponentialModule R) = r • (f : Additive R⟦X⟧) := rfl

noncomputable instance instModule : Module A (ExponentialModule R) where
  one_smul f := by rw [← Subtype.coe_inj, smul_def, one_smul]
  mul_smul r s f := by simp [← Subtype.coe_inj, smul_def, mul_smul]
  smul_zero r := by rw [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero, smul_zero]
  smul_add r f g := by simp [← Subtype.coe_inj, smul_def]
  add_smul r s f := by
    simp only [← Subtype.coe_inj, smul_def, AddSubmonoid.coe_add]
    apply Additive.toMul.injective
    simp [toAdditive_smul_coe', -toMul_val_eq_coe, f.prop.rescale_add r s]
  zero_smul f := by
    simp only [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero]
    apply Additive.toMul.injective
    have hf : constantCoeff f = (1 : R) := f.prop.constantCoeff
    simp [toAdditive_smul_coe', toMul_val_eq_coe, hf]

lemma coe_add (f g : ExponentialModule R) : (↑(f + g) : R⟦X⟧) = ↑f * ↑g := by
  simp only [toPowerSeries, AddSubmonoid.coe_add, toMul_add]

lemma coe_smul (r : A) (f : ExponentialModule R) :
    ((r • f) : ExponentialModule R) = rescale (algebraMap A R r) (f : R⟦X⟧) := rfl

end ExponentialModule

end CommSemiring

section CommRing

namespace IsExponential

variable [CommRing R] [CommSemiring S]

protected theorem neg {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (rescale  (-1 : R) f) := hf.rescale (-1 : R)

protected theorem self_mul_neg_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    f * (rescale (-1 : R) f) = 1 := by
  have hadd := hf.rescale_add (1 : R) (-1 : R)
  simp only [Algebra.algebraMap_self, RingHom.id_apply, add_neg_cancel, rescale_zero,
    RingHom.coe_comp, Function.comp_apply, rescale_one] at hadd
  rw [← hadd, hf.constantCoeff, map_one]

protected theorem neg_mul_self_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    (rescale (-1) f) * f = 1 := by rw [mul_comm, hf.self_mul_neg_eq_one]

protected theorem isUnit {f : R⟦X⟧} (hf : IsExponential f) : IsUnit f :=
  isUnit_iff_exists_inv'.mpr ⟨(rescale (-1) f),  hf.neg_mul_self_eq_one⟩

protected theorem inverse_eq_neg_mul_self {f : R⟦X⟧} (hf : IsExponential f) :
    Ring.inverse f = (rescale (-1) f) := by
  rw [Ring.inverse, dif_pos hf.isUnit]
  exact hf.isUnit.unit.inv_eq_of_mul_eq_one_left hf.neg_mul_self_eq_one

protected theorem invOfUnit_eq_rescale_neg_one {f : R⟦X⟧} (hf : IsExponential f) :
    (f.invOfUnit 1) = rescale (-1) f := by
  rw [← IsUnit.mul_right_inj hf.isUnit, f.mul_invOfUnit, hf.self_mul_neg_eq_one]
  simp [Units.val_one, hf.constantCoeff]

protected theorem inv {f : R⟦X⟧} (hf : IsExponential f) : IsExponential (f.invOfUnit 1) := by
  simp [hf.invOfUnit_eq_rescale_neg_one, hf.neg]

protected theorem map (φ : R →+* S) {f : R⟦X⟧} (hf : IsExponential f) :
    let _ : CommRing S := RingHom.commSemiringToCommRing φ
    IsExponential (PowerSeries.map φ f) := by
  let _ : CommRing S := RingHom.commSemiringToCommRing φ
  rw [isExponential_iff] at hf ⊢
  refine ⟨fun p q ↦ ?_, ?_⟩
  · simp only [coeff_map, ← map_mul, ← hf.1 p q]
    simp
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff, hf.2, map_one]

end IsExponential

namespace ExponentialModule

open PowerSeries Additive

variable [CommRing R]

noncomputable instance instAddCommGroup : AddCommGroup (ExponentialModule R) where
  neg f := (-1 : ℤ) • f
  zsmul n f := n • f
  zsmul_zero' f := by simp
  zsmul_succ' n f := by simp [add_smul]
  zsmul_neg' n f := by simp [Int.negSucc_eq, ← smul_assoc]
  neg_add_cancel f := by
    rw [← Subtype.coe_inj]
    apply Additive.toMul.injective
    simp only [AddSubmonoid.coe_add, toMul_add]
    rw [ZeroMemClass.coe_zero, toMul_zero, ← f.2.neg_mul_self_eq_one]
    simp [coe_smul]
  add_comm f g := add_comm f g

instance instIsScalarTower (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (ExponentialModule A) where
  smul_assoc r s f := by
    apply coe_injective
    simp only [coe_smul]
    rw [← algebraMap_smul S, smul_eq_mul, map_mul, mul_comm, rescale_mul]
    simp only [RingHom.coe_comp, Function.comp_apply]
    apply congr_fun
    ext f n
    simp [IsScalarTower.algebraMap_eq R S A, RingHom.coe_comp, Function.comp_apply]

lemma coe_ofMul (f : R⟦X⟧) (hf : IsExponential f) :
    ↑(⟨ofMul f, hf⟩ : ExponentialModule R) = f := rfl

lemma isExponential_coe (f : ExponentialModule R) : IsExponential (f : R⟦X⟧) := f.prop

lemma constantCoeff_coe (f : ExponentialModule R) : constantCoeff (f : R⟦X⟧) = 1 :=
  f.prop.constantCoeff

lemma subst_add_coe_eq_mul (f : ExponentialModule R) :
    subst (S := R) (X₀ + X₁) (f : R⟦X⟧) = (subst X₀ (f : R⟦X⟧)) * (subst X₁ (f : R⟦X⟧)) := by
  have hf := f.prop
  rw [mem_exponentialModule_iff'] at hf
  exact hf.add_mul

lemma choose_mul_coeff_add_eq (f : ExponentialModule R) (p q : ℕ) :
    (p + q).choose p * (coeff (p + q) (f : R⟦X⟧)) = coeff p f * coeff q f :=
  (subst_add_eq_mul_iff (R := R) f).mp (subst_add_coe_eq_mul f) p q

variable [CommRing A] [Algebra A R] {S : Type*} [CommRing S] [Algebra A S] (φ : R →ₐ[A] S)

/-- Given `A`-algebras `R` and `S`, this is the linear map between multivariate formal
power series induced by an `A`-algebra map on the coefficients.-/
noncomputable def linearMap :
    ExponentialModule R →ₗ[A] ExponentialModule S where
  toFun := fun f ↦
    ⟨ofMul (PowerSeries.map φ (f : R⟦X⟧)), by
      simp [mem_exponentialModule_iff]
      convert f.prop.map (φ  : R →+* S)
      ext <;> rfl⟩
  map_add' := fun f g ↦ coe_injective (by simp [coe_add])
  map_smul' := fun a f ↦
    coe_injective (by simp [-coe_mk, coe_smul, coe_ofMul, rescale_map_eq_map_rescale])

theorem coeff_linearMap (n : ℕ) (f : ExponentialModule R) :
    coeff n (linearMap φ f) = φ (coeff n f) := rfl

@[simp]
lemma coe_zero_eq_one (A : Type*) [CommRing A] :
    ((0 : ExponentialModule A) : A⟦X⟧) = 1 := by rfl

end ExponentialModule

end CommRing

end PowerSeries

--#lint
