/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Indicator

-/

section Preliminaries

open Finset Finsupp MvPowerSeries Nat

section CommSemiring

variable {R : Type*} [CommSemiring R]

section

namespace Finsupp

-- In #36441

variable {σ α : Type*} [Zero α] {f g : σ → α} {d : σ →₀ α}  {s t: Finset σ}

theorem indicator_indicator (f' : (i : σ) → i ∈ s → α) [DecidableEq σ] :
    indicator t (fun i _ ↦ indicator s f' i) =
      indicator (s ∩ t) (fun i hi ↦ f' i (Finset.mem_of_mem_inter_left hi)) := by
  ext i
  grind [indicator_apply]

theorem eq_indicator_iff (f' : (i : σ) → i ∈ s → α) :
    g = indicator s f' ↔ g.support ⊆ s ∧ ∀ i (hi : i ∈ s), f' i hi = g i := by
  classical
  suffices g.support ⊆ s ∧ (∀ i (hi : i ∈ s), f' i hi = g i) ↔
      (∀ i , if hi : i ∈ s then f' i hi = g i else g i = 0) by
    simp only [this, funext_iff, indicator_apply]
    grind
  rw [Set.subset_def, and_comm]
  have : (∀ (i : σ), if hi : i ∈ s then f' i hi = g i else g i = 0) ↔
      ((∀ (i : σ) (hi : i ∈ s),  f' i hi = g i) ∧ ∀ i (hi : i ∉ s), g i = 0) := by grind
  simp [this, not_imp_comm]

theorem eq_indicator_self_iff : (d = indicator s fun i _ ↦ d i) ↔ d.support ⊆ s := by
  grind [indicator]

-- Mathlib.Data.Nat.Choose.Multinomial
theorem multinomial_of_support_subset {d : σ →₀ ℕ} (h : d.support ⊆ s) :
    Nat.multinomial s d = d.multinomial := by
  rw [Nat.multinomial, Finsupp.multinomial,
    sum_of_support_subset _ h _ (by simp), prod_of_support_subset _ h _ (by simp)]
  simp

end Finsupp

end

namespace MvPolynomial

-- In #36444

open Finsupp

variable {σ : Type*} (d : σ →₀ ℕ) (x : σ → ℕ) (s : Finset σ)

theorem prod_X_pow :
    ∏ y ∈ s, (X y : MvPolynomial σ R) ^ x y = monomial (indicator s (fun i _ ↦ x i)) (1 : R) := by
  rw [monomial_eq, C_1, one_mul, prod,
    Finset.prod_subset (s₁ := (indicator s (fun i _ ↦ x i)).support) (s₂ := s)
      (support_indicator_subset _ _)]
  · exact Finset.prod_congr rfl (fun _ hi ↦ by simp [indicator, hi])
  · intro i hi hi'
    rw [Finsupp.mem_support_iff, ne_eq, not_not] at hi'
    rw [hi', pow_zero]

theorem coeff_prod_X_pow [DecidableEq σ] : coeff d (∏ y ∈ s, (X y : MvPolynomial σ R) ^ x y) =
      if d = indicator s (fun i _ ↦ x i) then 1 else 0 := by
  simp_rw [prod_X_pow x s, coeff_monomial, eq_comm]

variable {d} in
private theorem coeff_linearCombination_X_pow_of_eq (a : σ →₀ R) {n : ℕ}
    (hd : d.sum (fun _ m ↦ m) = n) :
    coeff d (((a.linearCombination R X : MvPolynomial σ R)) ^ n) =
      d.multinomial * d.prod (fun r m ↦ a r ^ m) := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_pow,
    ← map_prod, coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (d : σ → ℕ)]
  · simp_rw [eq_indicator_self_iff]
    split_ifs with hd'
    · rw [prod_of_support_subset _ hd' _ (by simp), multinomial_of_support_subset hd']
    · rw [Finset.subset_iff] at hd'
      simp only [Finsupp.mem_support_iff, ne_eq, not_forall, Decidable.not_not] at hd'
      obtain ⟨i, hdi, hai⟩ := hd'
      rw [← mul_prod_erase _ i _ (by simpa), hai, zero_pow hdi, zero_mul, mul_zero]
  · simp only [mem_piAntidiag, ne_eq, Finsupp.mem_support_iff, ite_eq_right_iff, and_imp]
    intro _ _ _ _ hed
    simp [Finsupp.ext_iff] at hed
    grind
  · simp_rw [ite_eq_right_iff]
    intro hd' hd''
    rw [eq_indicator_self_iff] at hd''
    exfalso
    rw [Finset.mem_piAntidiag, not_and_or] at hd'
    rcases hd' with hd' | hd'
    · apply hd'
      rw [← hd, sum_of_support_subset _ hd'' _ (by simp)]
    · grind

private theorem coeff_linearCombination_X_pow_of_ne {σ : Type*} (a : σ →₀ R) {d : σ →₀ ℕ} {n : ℕ}
    (hd : d.sum (fun _ m ↦ m) ≠ n) :
    coeff d (((a.linearCombination R X : MvPolynomial σ R)) ^ n) = 0 := by
  classical
  simp only [sum, linearCombination_apply, Finset.sum_pow_eq_sum_piAntidiag, coeff_sum, ← map_pow,
    ← C_eq_coe_nat, coeff_C_mul, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, ← map_prod,
    coeff_prod_X_pow, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_zero (fun x hx ↦ ?_)
  rw [if_neg]
  rintro ⟨rfl⟩
  apply hd
  simp only [mem_piAntidiag] at hx
  rw [sum_of_support_subset _ (support_indicator_subset a.support _) _ (by simp), ← hx.1]
  congr
  ext i
  by_cases hi : i ∈ a.support
  · simp [indicator_of_mem hi]
  · grind [indicator_of_notMem hi]

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
  rw [← ofSupportFinite_coe (f := a) (hf := Set.toFinite _),
    prod_congr (fun r _ ↦ rfl), ← coeff_linearCombination_X_pow]
  simp [linearCombination_apply, sum_of_support_subset (s := univ)]

theorem coeff_sum_X_pow_of_fintype {σ : Type*} [Fintype σ] (d : σ →₀ ℕ) (n : ℕ) :
    coeff d (((∑ i, X i : MvPolynomial σ R)) ^ n) =
      if d.sum (fun _ m ↦ m) = n then d.multinomial else 0 := by
  have : (∑ i, X i : MvPolynomial σ R) = ∑ i, (1 : σ → R) i • X i := by simp
  simp only [this, coeff_linearCombination_X_pow_of_fintype, Pi.one_apply, one_pow, cast_ite,
    cast_zero]
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
    simp [sum_of_support_subset d (subset_univ d.support)]
  simp only [mem_antidiagonal, this]
  split_ifs with hd
  · rw [multinomial_eq_of_support_subset (subset_univ d.support)]
    erw [Nat.binomial_eq_choose Fin.zero_ne_one]
    simp [hd]
  · rfl

end MvPolynomial

end CommSemiring

namespace PowerSeries

variable {A R S : Type*}

section Bivariate

-- In #37037

section CommSemiring

variable [CommSemiring A] [CommSemiring R] [Algebra A R] [CommSemiring S] [Algebra A S]

/-- Notation for the first variable of the bivariate power series ring `R⟦X₀, X₁⟧. -/
noncomputable abbrev X₀ {R : Type*} [Semiring R] := MvPowerSeries.X (σ := Fin 2) (R := R) 0

/-- Notation for the second variable of the bivariate power series ring `R⟦X₀, X₁⟧. -/
noncomputable abbrev X₁ {R : Type*} [Semiring R] := MvPowerSeries.X (σ := Fin 2) (R := R) 1

--Mathlib.Logic.Equiv.Fin.Basic
lemma forall_congr_curry {α : Type*} {p : (Fin 2 → α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 → α, p e ↔ q (e 0) (e 1)) :
    (∀ (e : Fin 2 → α), p e) ↔ ∀ (u v : α), q u v := by
  simp [Equiv.forall_congr_left (finTwoArrowEquiv α), hpq]

/- [Mathlib.Algebra.BigOperators.Finsupp.Fin,
 Mathlib.Algebra.Order.Antidiag.Finsupp,
 Mathlib.LinearAlgebra.Finsupp.Pi, Mathlib.Topology.Algebra.TopologicallyNilpotent,
 Mathlib.Topology.Algebra.Module.Basic, Mathlib.Data.Nat.Choose.Multinomial]
-/
lemma forall_congr_curry₀ {α : Type*} [Zero α] {p : (Fin 2 →₀ α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 →₀ α, p e ↔ q (e 0) (e 1)) :
    (∀ e, p e) ↔ ∀ u v, q u v := by
  simp [Equiv.forall_congr_left (equivFunOnFinite.trans (finTwoArrowEquiv α)), hpq]

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
    simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite,]
    grind

lemma coeff_subst_X₀_add_X₁ (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
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

lemma coeff_subst_X₀_mul_X₁ (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (subst X₀ f * subst X₁ f) = coeff (e 0) f * coeff (e 1) f := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (single 0 (e 0), single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
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
