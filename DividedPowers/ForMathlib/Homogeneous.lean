import DividedPowers.ForMathlib.WeightedHomogeneous
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Internal

noncomputable section

open scoped BigOperators

namespace MvPolynomial

variable {σ : Type _} {τ : Type _} {R : Type _} [CommSemiring R] {S : Type _}

/-- The degree of a monomial -/
def degree (d : σ →₀ ℕ) := ∑ i in d.support, d i

theorem degree_eq_weightedDegree' (d : σ →₀ ℕ) :
    ∑ i in d.support, d i = weightedDegree' 1 d := by
  simp [weightedDegree', Finsupp.total, Finsupp.sum]

theorem unit_weight_is_nonTrivialWeight : NonTrivialWeight (1 : σ → ℕ) :=
  nonTrivialWeight_of fun _ : σ => one_ne_zero

/-- A multivariate polynomial `φ` is homogeneous of degree `n`
if all monomials occuring in `φ` have degree `n`. -/
def IsHomogeneous (φ : MvPolynomial σ R) (n : ℕ) :=
  IsWeightedHomogeneous 1 φ n
#align mv_polynomial.is_homogeneous MvPolynomial.IsHomogeneous

variable (σ R)

theorem totalDegree_eq_weightedTotalDegree (φ : MvPolynomial σ R) :
    φ.totalDegree = weightedTotalDegree (1 : σ → ℕ) φ := by
  simp only [totalDegree, weightedTotalDegree, weightedDegree', LinearMap.toAddMonoidHom_coe,
    Finsupp.total, Pi.one_apply, Finsupp.coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, 
    id.def, Algebra.id.smul_eq_mul, mul_one]
#align mv_polynomial.total_degree_eq_weighted_total_degree
  MvPolynomial.totalDegree_eq_weightedTotalDegree

/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def homogeneousSubmodule (n : ℕ) : Submodule R (MvPolynomial σ R) :=
  weightedHomogeneousSubmodule R (1 : σ → ℕ) n
#align mv_polynomial.homogeneous_submodule MvPolynomial.homogeneousSubmodule


variable {σ R}

@[simp]
theorem mem_homogeneousSubmodule (n : ℕ) (p : MvPolynomial σ R) :
    p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n :=
  Iff.rfl
#align mv_polynomial.mem_homogeneous_submodule MvPolynomial.mem_homogeneousSubmodule


variable (σ R)

/-- While equal, the former has a convenient definitional reduction. -/
theorem homogeneousSubmodule_eq_finsupp_supported (n : ℕ) :
    homogeneousSubmodule σ R n = Finsupp.supported _ R {d | ∑ i in d.support, d i = n} :=
  by
  simp_rw [degree_eq_weightedDegree']
  exact weightedHomogeneousSubmodule_eq_finsupp_supported R 1 n
#align mv_polynomial.homogeneous_submodule_eq_finsupp_supported
  MvPolynomial.homogeneousSubmodule_eq_finsupp_supported


variable {σ R}

theorem homogeneousSubmodule_mul (m n : ℕ) :
    homogeneousSubmodule σ R m * homogeneousSubmodule σ R n ≤ homogeneousSubmodule σ R (m + n) :=
  weightedHomogeneousSubmodule_mul (1 : σ → ℕ) m n
#align mv_polynomial.homogeneous_submodule_mul MvPolynomial.homogeneousSubmodule_mul

section

theorem isHomogeneous_monomial (d : σ →₀ ℕ) (r : R) (n : ℕ)
    (hn : ∑ i in d.support, d i = n) : IsHomogeneous (monomial d r) n := by
  simp_rw [degree_eq_weightedDegree'] at hn 
  exact isWeightedHomogeneous_monomial 1 d r hn
#align mv_polynomial.is_homogeneous_monomial MvPolynomial.isHomogeneous_monomial

variable (σ)

theorem totalDegree_eq_zero_iff (p : MvPolynomial σ R) :
    p.totalDegree = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = 0 := by
  rw [totalDegree_eq_weightedTotalDegree, weightedTotalDegree_eq_zero_iff _ p] 
  simp_rw [bot_eq_zero'] 
  exact unit_weight_is_nonTrivialWeight
#align mv_polynomial.total_degree_eq_zero_iff MvPolynomial.totalDegree_eq_zero_iff

/- 
begin
  rw [total_degree, ← bot_eq_zero, finset.sup_eq_bot_iff, bot_eq_zero], 
  apply forall_congr, intro a, 
  apply forall_congr, intro hap,
  simp only [finsupp.sum, finset.sum_eq_zero_iff, finsupp.mem_support_iff],
  apply forall_congr, 
  intro x, 
  simp only [not_imp_self],
end
 -/
theorem isHomogeneous_of_totalDegree_zero_iff {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ IsHomogeneous p 0 := by
  rw [totalDegree_eq_weightedTotalDegree,
    ← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsHomogeneous]
#align mv_polynomial.is_homogeneous_of_total_degree_zero_iff
  MvPolynomial.isHomogeneous_of_totalDegree_zero_iff

theorem isHomogeneous_of_totalDegree_zero {p : MvPolynomial σ R} (hp : p.totalDegree = 0) :
    IsHomogeneous p 0 :=
  (isHomogeneous_of_totalDegree_zero_iff σ).mp hp
#align mv_polynomial.is_homogeneous_of_total_degree_zero
  MvPolynomial.isHomogeneous_of_totalDegree_zero

set_option linter.uppercaseLean3 false
theorem isHomogeneous_C (r : R) : IsHomogeneous (C r : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_C (1 : σ → ℕ) r
#align mv_polynomial.is_homogeneous_C MvPolynomial.isHomogeneous_C

variable (R)

theorem isHomogeneous_zero (n : ℕ) : IsHomogeneous (0 : MvPolynomial σ R) n :=
  isWeightedHomogeneous_zero R (1 : σ → ℕ) n
#align mv_polynomial.is_homogeneous_zero MvPolynomial.isHomogeneous_zero

theorem isHomogeneous_one : IsHomogeneous (1 : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_one R (1 : σ → ℕ)
#align mv_polynomial.is_homogeneous_one MvPolynomial.isHomogeneous_one

variable {σ}

theorem isHomogeneous_X  (i : σ) : IsHomogeneous (X i : MvPolynomial σ R) 1 :=
  isWeightedHomogeneous_X R (1 : σ → ℕ) i
#align mv_polynomial.is_homogeneous_X MvPolynomial.isHomogeneous_X

end

namespace IsHomogeneous

variable {φ ψ : MvPolynomial σ R} {m n : ℕ}

theorem coeff_eq_zero (hφ : IsHomogeneous φ n) (d : σ →₀ ℕ) (hd : ∑ i in d.support, d i ≠ n) :
    coeff d φ = 0 := by
  simp_rw [degree_eq_weightedDegree'] at hd
  exact IsWeightedHomogeneous.coeff_eq_zero hφ d hd
#align mv_polynomial.is_homogeneous.coeff_eq_zero MvPolynomial.IsHomogeneous.coeff_eq_zero

theorem inj_right (hm : IsHomogeneous φ m) (hn : IsHomogeneous φ n) (hφ : φ ≠ 0) : m = n :=
  IsWeightedHomogeneous.inj_right hφ hm hn
#align mv_polynomial.is_homogeneous.inj_right MvPolynomial.IsHomogeneous.inj_right

theorem add (hφ : IsHomogeneous φ n) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ + ψ) n :=
  IsWeightedHomogeneous.add hφ hψ
#align mv_polynomial.is_homogeneous.add MvPolynomial.IsHomogeneous.add

theorem sum {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ℕ)
    (h : ∀ i ∈ s, IsHomogeneous (φ i) n) : IsHomogeneous (∑ i in s, φ i) n :=
  IsWeightedHomogeneous.sum s φ n h
#align mv_polynomial.is_homogeneous.sum MvPolynomial.IsHomogeneous.sum

theorem mul (hφ : IsHomogeneous φ m) (hψ : IsHomogeneous ψ n) : IsHomogeneous (φ * ψ) (m + n) :=
  IsWeightedHomogeneous.mul hφ hψ
#align mv_polynomial.is_homogeneous.mul MvPolynomial.IsHomogeneous.mul

theorem prod {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → ℕ) 
    (h : ∀ i ∈ s, IsHomogeneous (φ i) (n i)) : IsHomogeneous (∏ i in s, φ i) (∑ i in s, n i) :=
  IsWeightedHomogeneous.prod s φ n h
#align mv_polynomial.is_homogeneous.prod MvPolynomial.IsHomogeneous.prod


theorem totalDegree_eq_weightedTotalDegree : totalDegree φ = weightedTotalDegree (1 : σ → ℕ) φ :=
  by
  rw [totalDegree, weightedTotalDegree, weightedDegree']
  apply Finset.sup_congr rfl
  intro a _
  simp only [Finsupp.total, Pi.one_apply, LinearMap.toAddMonoidHom_coe, Finsupp.coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id.def, Algebra.id.smul_eq_mul, mul_one]
#align mv_polynomial.is_homogeneous.total_degree_eq_weighted_total_degree
  MvPolynomial.IsHomogeneous.totalDegree_eq_weightedTotalDegree

theorem totalDegree (hφ : IsHomogeneous φ n) (h : φ ≠ 0) : totalDegree φ = n := by
  rw [totalDegree_eq_weightedTotalDegree, ← WithBot.coe_eq_coe, ←
    weightedTotalDegree_coe _ φ h, IsWeightedHomogeneous.weighted_total_degree hφ h]
#align mv_polynomial.is_homogeneous.total_degree MvPolynomial.IsHomogeneous.totalDegree

/-- The homogeneous submodules form a graded ring. 
This instance is used by `direct_sum.comm_semiring` and `direct_sum.algebra`. -/
instance HomogeneousSubmodule.gcomm_monoid [DecidableEq σ] :
    SetLike.GradedMonoid (homogeneousSubmodule σ R) :=
  IsWeightedHomogeneous.WeightedHomogeneousSubmodule.gcomm_monoid
#align mv_polynomial.is_homogeneous.homogeneous_submodule.gcomm_monoid
  MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcomm_monoid

open scoped DirectSum

/- 
noncomputable example : 
  direct_sum.gcomm_semiring [decidable_eq σ] (λ i, homogeneous_submodule σ R i) := 
begin
-- apply direct_sum.comm_semiring , 
  haveI : set_like.graded_monoid (λ (i : ℕ), homogeneous_submodule σ R i),
  apply is_weighted_homogeneous.weighted_homogeneous_submodule.gcomm_monoid, 
apply set_like.gcomm_semiring, 
sorry,
end
-/
--noncomputable example : algebra R (⨁ i, homogeneous_submodule σ R i) := sorry --infer_instance
end IsHomogeneous

section

noncomputable section

-- open_locale classical
open Finset

--variable (R)

/-- `homogeneous_component n φ` is the part of `φ` that is homogeneous of degree `n`.
See `sum_homogeneous_component` for the statement that `φ` is equal to the sum
of all its homogeneous components. -/
def homogeneousComponent (n : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  weightedHomogeneousComponent (1 : σ → ℕ) n
#align mv_polynomial.homogeneous_component MvPolynomial.homogeneousComponent

--variable {R}

theorem homogeneousComponent_mem (φ : MvPolynomial σ R) (i : ℕ) :
    homogeneousComponent i φ ∈ homogeneousSubmodule σ R i :=
  weightedHomogeneousComponent_mem _ φ i
#align mv_polynomial.homogeneous_component_mem MvPolynomial.homogeneousComponent_mem

section HomogeneousComponent

open Finset

variable (n : ℕ) (φ ψ : MvPolynomial σ R)

theorem coeff_homogeneousComponent (d : σ →₀ ℕ) :
    coeff d (homogeneousComponent n φ) = if ∑ i in d.support, d i = n then coeff d φ else 0 :=
  by
  simp_rw [degree_eq_weightedDegree']
  convert coeff_weightedHomogeneousComponent n φ d
#align mv_polynomial.coeff_homogeneous_component MvPolynomial.coeff_homogeneousComponent

theorem homogeneousComponent_apply :
    homogeneousComponent n φ =
      ∑ d in φ.support.filter fun d => ∑ i in d.support, d i = n, monomial d (coeff d φ) :=
  by
  simp_rw [degree_eq_weightedDegree']
  convert weightedHomogeneousComponent_apply n φ
#align mv_polynomial.homogeneous_component_apply MvPolynomial.homogeneousComponent_apply

theorem homogeneousComponent_isHomogeneous : (homogeneousComponent n φ).IsHomogeneous n :=
  weightedHomogeneousComponent_isWeightedHomogeneous n φ
#align mv_polynomial.homogeneous_component_is_homogeneous
  MvPolynomial.homogeneousComponent_isHomogeneous

@[simp]
theorem homogeneousComponent_zero : homogeneousComponent  0 φ = C (coeff 0 φ) :=
  weightedHomogeneousComponent_zero φ (fun _ => Nat.succ_ne_zero Nat.zero)
#align mv_polynomial.homogeneous_component_zero MvPolynomial.homogeneousComponent_zero

set_option linter.uppercaseLean3 false
@[simp] theorem homogeneousComponent_C_mul (n : ℕ) (r : R) :
    homogeneousComponent n (C r * φ) = C r * homogeneousComponent n φ :=
  weightedHomogeneousComponent_C_mul φ n r
#align mv_polynomial.homogeneous_component_C_mul MvPolynomial.homogeneousComponent_C_mul

theorem homogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → ∑ i in d.support, d i ≠ n) :
    homogeneousComponent n φ = 0 :=
  by
  simp_rw [degree_eq_weightedDegree'] at h 
  exact weightedHomogeneousComponent_eq_zero' n φ h
#align mv_polynomial.homogeneous_component_eq_zero' MvPolynomial.homogeneousComponent_eq_zero'

--TODO: change proof when `weighted_total_degree` exists.
theorem homogeneousComponent_eq_zero (h : φ.totalDegree < n) : homogeneousComponent n φ = 0 := by
  apply homogeneousComponent_eq_zero'
  rw [totalDegree, Finset.sup_lt_iff] at h 
  · intro d hd; exact ne_of_lt (h d hd)
  · exact lt_of_le_of_lt (Nat.zero_le _) h
#align mv_polynomial.homogeneous_component_eq_zero MvPolynomial.homogeneousComponent_eq_zero

--TODO: change proof when `weighted_total_degree` exists.
theorem sum_homogeneousComponent :
    ∑ i in range (φ.totalDegree + 1), homogeneousComponent i φ = φ := by
  ext1 d
  suffices φ.totalDegree < d.support.sum d → 0 = coeff d φ by
    simpa [coeff_sum, coeff_homogeneousComponent]
  exact fun h => (coeff_eq_zero_of_totalDegree_lt h).symm
#align mv_polynomial.sum_homogeneous_component MvPolynomial.sum_homogeneousComponent

theorem homogeneousComponent_homogeneous_polynomial (m n : ℕ) (p : MvPolynomial σ R)
    (h : p ∈ homogeneousSubmodule σ R n) : homogeneousComponent m p = if m = n then p else 0 := by
  convert weightedHomogeneousComponent_weighted_homogeneous_polynomial m n p h
#align mv_polynomial.homogeneous_component_homogeneous_polynomial
  MvPolynomial.homogeneousComponent_homogeneous_polynomial

end HomogeneousComponent

end

section GradedAlgebra

variable (σ)

/-- The decomposition of mv_polynomial σ R into  homogeneous submodules -/
def decomposition [DecidableEq σ] [DecidableEq R] :
    DirectSum.Decomposition (homogeneousSubmodule σ R) :=
  weightedDecomposition R (1 : σ → ℕ)
#align mv_polynomial.decomposition MvPolynomial.decomposition

/-- Given a weight, mv_polynomial as a graded algebra -/
def gradedAlgebra [DecidableEq σ] [DecidableEq R] : GradedAlgebra (homogeneousSubmodule σ R) :=
  weightedGradedAlgebra R (1 : σ → ℕ)
#align mv_polynomial.graded_algebra MvPolynomial.gradedAlgebra

theorem decomposition.decompose'_eq [DecidableEq σ] [DecidableEq R] :
    (decomposition σ).decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : ℕ => ↥(homogeneousSubmodule σ R i)) (Finset.image degree' φ.support)
        fun m => ⟨homogeneousComponent m φ, homogeneousComponent_mem φ m⟩ := by
  sorry --rfl does not work anymore (?)
#align mv_polynomial.decomposition.decompose'_eq MvPolynomial.decomposition.decompose'_eq

theorem decomposition.decompose'_apply [DecidableEq σ] [DecidableEq R] (φ : MvPolynomial σ R)
    (i : ℕ) : ((decomposition σ).decompose' φ i : MvPolynomial σ R) = homogeneousComponent i φ :=
  weightedDecomposition.decompose'_apply R _ φ i
#align mv_polynomial.decomposition.decompose'_apply MvPolynomial.decomposition.decompose'_apply

end GradedAlgebra