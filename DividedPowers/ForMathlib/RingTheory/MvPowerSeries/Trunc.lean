import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Interval



noncomputable section

open BigOperators

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

-- LE version of trunc
section Trunc'

variable [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun' (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m in Finset.Iic n, MvPolynomial.monomial m (coeff R m φ)

theorem coeff_truncFun' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun' n φ).coeff m = if m ≤ n then coeff R m φ else 0 := by
  classical
  simp [truncFun', MvPolynomial.coeff_sum]

variable (R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def trunc' : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun' n
  map_zero' := by
    classical
    ext
    simp [coeff_truncFun']
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun', MvPolynomial.coeff_add]
    split_ifs
    · rw [map_add]
    · rw [zero_add]

variable {R}

theorem coeff_trunc' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m ≤ n then coeff R m φ else 0 :=
    -- by classical simp [trunc', coeff_truncFun']
  coeff_truncFun' n m φ

@[simp]
theorem trunc_one' (n : σ →₀ ℕ) : trunc' R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc', coeff_one]
    split_ifs with H H'
    · subst m
      simp
    · symm
      rw [MvPolynomial.coeff_one]
      exact if_neg (Ne.symm H')
    · symm
      rw [MvPolynomial.coeff_one]
      refine' if_neg _
      rintro rfl
      apply H
      exact orderBot.proof_1 n

@[simp]
theorem trunc_c (n : σ →₀ ℕ) (a : R) : trunc' R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc', coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first |rfl|try simp_all
    exfalso; apply H; subst m; exact orderBot.proof_1 n

theorem coeff_mul_trunc' (n : σ →₀ ℕ) (f g : MvPowerSeries σ R)
    {m : σ →₀ ℕ} (h : m ≤ n) :
    ((trunc' R n f) * (trunc' R n g)).coeff m = coeff R m (f * g) := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [← hij] at h
  simp only
  apply congr_arg₂
  rw [coeff_trunc', if_pos (le_trans le_self_add h)]
  rw [coeff_trunc', if_pos (le_trans le_add_self h)]

end Trunc'

end MvPowerSeries

end
