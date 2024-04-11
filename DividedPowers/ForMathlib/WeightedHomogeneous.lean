/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández

! This file was ported from Lean 3 source module weighted_homogeneous
-/

/- TODO :

1) There is one complicated "convert" -
it probably deserves a lemma that does the rewrite in an easy way
(`rw` sufficed in mathlib3)

2) I (ACL) removed all `classical` and the `instance` that we had added - the 3 natural `DecidableEq` assumptions (on variables, weights and coefficients) suffice.

-/

import DividedPowers.ForMathlib.GradedAlgebra

import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Weighted homogeneous polynomials

It is possible to assign weights (in a commutative additive monoid `M`) to the variables of a
multivariate polynomial ring, so that monomials of the ring then have a weighted degree with
respect to the weights of the variables. The weights are represented by a function `w : σ → M`,
where `σ` are the indeterminates.

A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m : M` if all monomials
occuring in `φ` have the same weighted degree `m`.

## Main definitions/lemmas

* `weighted_total_degree' w φ` : the weighted total degree of a multivariate polynomial with respect
to the weights `w`, taking values in `with_bot M`.

* `weighted_total_degree w φ` : When `M` has a `⊥` element, we can define the weighted total degree
of a multivariate polynomial as a function taking values in `M`.

* `is_weighted_homogeneous w φ m`: a predicate that asserts that `φ` is weighted homogeneous
of weighted degree `m` with respect to the weights `w`.

* `weighted_homogeneous_submodule R w m`: the submodule of homogeneous polynomials
of weighted degree `m`.

* `weighted_homogeneous_component w m`: the additive morphism that projects polynomials
onto their summand that is weighted homogeneous of degree `n` with respect to `w`.

* `sum_weighted_homogeneous_component`: every polynomial is the sum of its weighted homogeneous
components.
-/


/- WARNING :
This is a modified version of ring_theory.mv_polynomial.weighted_homogeneous

The main modifications are indicated by MODIF

-/
noncomputable section

-- MODIF: remove classical and add adequate decidable instances
open scoped BigOperators

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type _} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type _}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weighted_degree'` -/


-- #print MvPolynomial.weightedDegree'
/-
-- MODIF: remove .to_add_monoid_hom
/-- The `weighted degree'` of the finitely supported function `s : σ →₀ ℕ` is the sum
  `∑(s i)•(w i)`. -/
def weightedDegree' (w : σ → M) : (σ →₀ ℕ) →ₗ[ℕ] M :=
  Finsupp.total σ M ℕ w
#align mv_polynomial.weighted_degree' MvPolynomial.weightedDegree'
-/

theorem weightedDegree'_apply (w : σ → M) (f : σ →₀ ℕ):
  weightedDegree' w f = Finsupp.sum f (fun i c => c • w i) := by
  rfl

section SemilatticeSup

variable [SemilatticeSup M]

-- #print MvPolynomial.weightedTotalDegree'

/-
/-- The weighted total degree of a multivariate polynomial, taking values in `with_bot M`. -/
def weightedTotalDegree' (w : σ → M) (p : MvPolynomial σ R) : WithBot M :=
  p.support.sup fun s => weightedDegree' w s
#align mv_polynomial.weighted_total_degree' MvPolynomial.weightedTotalDegree'
-/

-- #print MvPolynomial.weightedTotalDegree'_eq_bot_iff
/-
/-- The `weighted_total_degree'` of a polynomial `p` is `⊥` if and only if `p = 0`. -/
theorem weightedTotalDegree'_eq_bot_iff (w : σ → M) (p : MvPolynomial σ R) :
    weightedTotalDegree' w p = ⊥ ↔ p = 0 :=
  by
  simp only [weighted_total_degree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not
#align mv_polynomial.weighted_total_degree'_eq_bot_iff MvPolynomial.weightedTotalDegree'_eq_bot_iff
-/

-- #print MvPolynomial.weightedTotalDegree'_zero
/-
/-- The `weighted_total_degree'` of the zero polynomial is `⊥`. -/
theorem weightedTotalDegree'_zero (w : σ → M) : weightedTotalDegree' w (0 : MvPolynomial σ R) = ⊥ :=
  by simp only [weighted_total_degree', support_zero, Finset.sup_empty]
#align mv_polynomial.weighted_total_degree'_zero MvPolynomial.weightedTotalDegree'_zero
-/

section OrderBot

variable [OrderBot M]

-- #print MvPolynomial.weightedTotalDegree
/-
/-- When `M` has a `⊥` element, we can define the weighted total degree of a multivariate
  polynomial as a function taking values in `M`. -/
def weightedTotalDegree (w : σ → M) (p : MvPolynomial σ R) : M :=
  p.support.sup fun s => weightedDegree' w s
#align mv_polynomial.weighted_total_degree MvPolynomial.weightedTotalDegree
-/

-- #print MvPolynomial.weightedTotalDegree_coe
/-
/-- This lemma relates `weighted_total_degree` and `weighted_total_degree'`. -/
theorem weightedTotalDegree_coe (w : σ → M) (p : MvPolynomial σ R) (hp : p ≠ 0) :
    weightedTotalDegree' w p = ↑(weightedTotalDegree w p) :=
  by
  rw [Ne.def, ← weighted_total_degree'_eq_bot_iff w p, ← Ne.def, WithBot.ne_bot_iff_exists] at hp
  obtain ⟨m, hm⟩ := hp
  apply le_antisymm
  · simp only [weighted_total_degree, weighted_total_degree', Finset.sup_le_iff, WithBot.coe_le_coe]
    intro b
    exact Finset.le_sup
  · simp only [weighted_total_degree]
    have hm' : weighted_total_degree' w p ≤ m := le_of_eq hm.symm
    rw [← hm]
    simpa [weighted_total_degree'] using hm'
#align mv_polynomial.weighted_total_degree_coe MvPolynomial.weightedTotalDegree_coe
-/

-- #print MvPolynomial.weightedTotalDegree_zero
/-
/-- The `weighted_total_degree` of the zero polynomial is `⊥`. -/
theorem weightedTotalDegree_zero (w : σ → M) : weightedTotalDegree w (0 : MvPolynomial σ R) = ⊥ :=
  by simp only [weighted_total_degree, support_zero, Finset.sup_empty]
#align mv_polynomial.weighted_total_degree_zero MvPolynomial.weightedTotalDegree_zero
-/

-- #print MvPolynomial.le_weightedTotalDegree
/-
theorem le_weightedTotalDegree (w : σ → M) {φ : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ φ.support) : weightedDegree' w d ≤ φ.weightedTotalDegree w :=
  le_sup hd
#align mv_polynomial.le_weighted_total_degree MvPolynomial.le_weightedTotalDegree
-/

end OrderBot

end SemilatticeSup

-- #print MvPolynomial.IsWeightedHomogeneous
/-
/-- A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m` if all monomials
  occuring in `φ` have weighted degree `m`. -/
def IsWeightedHomogeneous (w : σ → M) (φ : MvPolynomial σ R) (m : M) : Prop :=
  ∀ ⦃d⦄, coeff d φ ≠ 0 → weightedDegree' w d = m
#align mv_polynomial.is_weighted_homogeneous MvPolynomial.IsWeightedHomogeneous
-/

variable (R)

-- #print MvPolynomial.weightedHomogeneousSubmodule
/-
/-- The submodule of homogeneous `mv_polynomial`s of degree `n`. -/
def weightedHomogeneousSubmodule (w : σ → M) (m : M) : Submodule R (MvPolynomial σ R)
    where
  carrier := {x | x.IsWeightedHomogeneous w m}
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' d hd := False.elim (hd <| coeff_zero _)
  add_mem' a b ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a ≠ 0 ∨ coeff c b ≠ 0 := by contrapose! hc; simp only [hc, add_zero]
    · exact ha h
    · exact hb h
#align mv_polynomial.weighted_homogeneous_submodule MvPolynomial.weightedHomogeneousSubmodule
-/

-- #print MvPolynomial.mem_weightedHomogeneousSubmodule
/-
@[simp]
theorem mem_weightedHomogeneousSubmodule (w : σ → M) (m : M) (p : MvPolynomial σ R) :
    p ∈ weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m :=
  Iff.rfl
#align mv_polynomial.mem_weighted_homogeneous_submodule MvPolynomial.mem_weightedHomogeneousSubmodule
-/

-- variable (R) -- redundant

-- #print MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported
/-
/-- The submodule ` weighted_homogeneous_submodule R w m` of homogeneous `mv_polynomial`s of
  degree `n` is equal to the `R`-submodule of all `p : (σ →₀ ℕ) →₀ R` such that
  `p.support ⊆ {d | weighted_degree' w d = m}`. While equal, the former has a
  convenient definitional reduction. -/
theorem weightedHomogeneousSubmodule_eq_finsupp_supported (w : σ → M) (m : M) :
    weightedHomogeneousSubmodule R w m = Finsupp.supported _ R {d | weightedDegree' w d = m} :=
  by
  ext
  simp only [mem_supported, Set.subset_def, Finsupp.mem_support_iff, mem_coe]
  rfl
#align mv_polynomial.weighted_homogeneous_submodule_eq_finsupp_supported MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported
-/

variable {R}

-- #print MvPolynomial.weightedHomogeneousSubmodule_mul
/-
/-- The submodule generated by products `Pm *Pn` of weighted homogeneous polynomials of degrees `m`
  and `n` is contained in the submodule of weighted homogeneous polynomials of degree `m + n`. -/
theorem weightedHomogeneousSubmodule_mul (w : σ → M) (m n : M) :
    weightedHomogeneousSubmodule R w m * weightedHomogeneousSubmodule R w n ≤
      weightedHomogeneousSubmodule R w (m + n) :=
  by
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ ≠ 0 ∧ coeff e ψ ≠ 0 :=
    by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne.def, not_false_iff, MulZeroClass.zero_mul, MulZeroClass.mul_zero]
  rw [← finsupp.mem_antidiagonal.mp hde, ← hφ aux.1, ← hψ aux.2, map_add]
#align mv_polynomial.weighted_homogeneous_submodule_mul MvPolynomial.weightedHomogeneousSubmodule_mul
-/

-- #print MvPolynomial.isWeightedHomogeneous_monomial
/-
-- The linter complains if you add [decidable_eq σ]
-- MODIF: add [decidable_eq σ]
/-- Monomials are weighted homogeneous. -/
theorem isWeightedHomogeneous_monomial (w : σ → M) (d : σ →₀ ℕ) (r : R) {m : M}
    (hm : weightedDegree' w d = m) : IsWeightedHomogeneous w (monomial d r) m := by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc  with h
  · subst c; exact hm
  · contradiction
#align mv_polynomial.is_weighted_homogeneous_monomial MvPolynomial.isWeightedHomogeneous_monomial
-/

-- #print MvPolynomial.isWeightedHomogeneous_of_total_degree_zero
/-
/-- A polynomial of weighted_total_degree `⊥` is weighted_homogeneous of degree `⊥`. -/
theorem isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M] (w : σ → M)
    {p : MvPolynomial σ R} (hp : weightedTotalDegree w p = (⊥ : M)) :
    IsWeightedHomogeneous w p (⊥ : M) := by
  intro d hd
  have h := weighted_total_degree_coe w p (mv_polynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  simp only [weighted_total_degree', hp] at h
  rw [eq_bot_iff, ← WithBot.coe_le_coe, ← h]
  exact Finset.le_sup (mem_support_iff.mpr hd)
#align mv_polynomial.is_weighted_homogeneous_of_total_degree_zero MvPolynomial.isWeightedHomogeneous_of_total_degree_zero
-/

-- #print MvPolynomial.isWeightedHomogeneous_C
/-
/-- Constant polynomials are weighted homogeneous of degree 0. -/
theorem isWeightedHomogeneous_C (w : σ → M) (r : R) :
    IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_monomial _ _ _ (map_zero _)
#align mv_polynomial.is_weighted_homogeneous_C MvPolynomial.isWeightedHomogeneous_C
-/

variable (R)

-- #print MvPolynomial.isWeightedHomogeneous_zero
/-
/-- 0 is weighted homogeneous of any degree. -/
theorem isWeightedHomogeneous_zero (w : σ → M) (m : M) :
    IsWeightedHomogeneous w (0 : MvPolynomial σ R) m :=
  (weightedHomogeneousSubmodule R w m).zero_mem
#align mv_polynomial.is_weighted_homogeneous_zero MvPolynomial.isWeightedHomogeneous_zero
-/

-- #print MvPolynomial.isWeightedHomogeneous_one
/-
/-- 1 is weighted homogeneous of degree 0. -/
theorem isWeightedHomogeneous_one (w : σ → M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_C _ _
#align mv_polynomial.is_weighted_homogeneous_one MvPolynomial.isWeightedHomogeneous_one
-/

-- #print MvPolynomial.isWeightedHomogeneous_X
/-
/-- An indeterminate `i : σ` is weighted homogeneous of degree `w i`. -/
theorem isWeightedHomogeneous_X (w : σ → M) (i : σ) :
    IsWeightedHomogeneous w (X i : MvPolynomial σ R) (w i) :=
  by
  apply is_weighted_homogeneous_monomial
  simp only [weighted_degree', AddMonoidHom.coe_coe, total_single, one_nsmul]
#align mv_polynomial.is_weighted_homogeneous_X MvPolynomial.isWeightedHomogeneous_X
-/

namespace IsWeightedHomogeneous

variable {R}
variable {φ ψ : MvPolynomial σ R} {m n : M}

-- #print MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero
/-
/-- The weighted degree of a weighted homogeneous polynomial controls its support. -/
theorem coeff_eq_zero {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (d : σ →₀ ℕ)
    (hd : weightedDegree' w d ≠ n) : coeff d φ = 0 := by have aux := mt (@hφ d) hd;
  rwa [Classical.not_not] at aux
#align mv_polynomial.is_weighted_homogeneous.coeff_eq_zero MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero
-/

-- #print MvPolynomial.IsWeightedHomogeneous.inj_right
/-
/-- The weighted degree of a nonzero weighted homogeneous polynomial is well-defined. -/
theorem inj_right {w : σ → M} (hφ : φ ≠ 0) (hm : IsWeightedHomogeneous w φ m)
    (hn : IsWeightedHomogeneous w φ n) : m = n :=
  by
  obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero hφ
  rw [← hm hd, ← hn hd]
#align mv_polynomial.is_weighted_homogeneous.inj_right MvPolynomial.IsWeightedHomogeneous.inj_right
-/

-- #print MvPolynomial.IsWeightedHomogeneous.add
/-
/-- The sum of two weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
theorem add {w : σ → M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ + ψ) n :=
  (weightedHomogeneousSubmodule R w n).add_mem hφ hψ
#align mv_polynomial.is_weighted_homogeneous.add MvPolynomial.IsWeightedHomogeneous.add
-/

-- #print MvPolynomial.IsWeightedHomogeneous.sum
/-
/-- The sum of weighted homogeneous polynomials of degree `n` is weighted homogeneous of
  weighted degree `n`. -/
theorem sum {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : M) {w : σ → M}
    (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i in s, φ i) n :=
  (weightedHomogeneousSubmodule R w n).sum_mem h
#align mv_polynomial.is_weighted_homogeneous.sum MvPolynomial.IsWeightedHomogeneous.sum
-/

-- #print MvPolynomial.IsWeightedHomogeneous.mul
/-
/-- The product of weighted homogeneous polynomials of weighted degrees `m` and `n` is weighted
  homogeneous of weighted degree `m + n`. -/
theorem mul {w : σ → M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ * ψ) (m + n) :=
  weightedHomogeneousSubmodule_mul w m n <| Submodule.mul_mem_mul hφ hψ
#align mv_polynomial.is_weighted_homogeneous.mul MvPolynomial.IsWeightedHomogeneous.mul
-/

-- #print MvPolynomial.IsWeightedHomogeneous.prod
/-
/-- A product of weighted homogeneous polynomials is weighted homogeneous, with weighted degree
  equal to the sum of the weighted degrees. -/
theorem prod {ι : Type _} (s : Finset ι) (φ : ι → MvPolynomial σ R) (n : ι → M) {w : σ → M} :
    (∀ i ∈ s, IsWeightedHomogeneous w (φ i) (n i)) →
      IsWeightedHomogeneous w (∏ i in s, φ i) (∑ i in s, n i) :=
  by
  classical
  apply Finset.induction_on s
  · intro
    rw [Finset.sum_empty, Finset.prod_empty]
    exact is_weighted_homogeneous_one R w
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)
#align mv_polynomial.is_weighted_homogeneous.prod MvPolynomial.IsWeightedHomogeneous.prod
-/

-- #print MvPolynomial.IsWeightedHomogeneous.weighted_total_degree
/-
/-- A non zero weighted homogeneous polynomial of weighted degree `n` has weighted total degree
  `n`. -/
theorem weighted_total_degree [SemilatticeSup M] {w : σ → M} (hφ : IsWeightedHomogeneous w φ n)
    (h : φ ≠ 0) : weightedTotalDegree' w φ = n :=
  by
  simp only [weighted_total_degree']
  apply le_antisymm
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    exact fun d hd => le_of_eq (hφ hd)
  · obtain ⟨d, hd⟩ : ∃ d, coeff d φ ≠ 0 := exists_coeff_ne_zero h
    simp only [← hφ hd, Finsupp.sum]
    replace hd := finsupp.mem_support_iff.mpr hd
    exact Finset.le_sup hd
#align mv_polynomial.is_weighted_homogeneous.weighted_total_degree MvPolynomial.IsWeightedHomogeneous.weighted_total_degree
-/

-- #print MvPolynomial.IsWeightedHomogeneous.WeightedHomogeneousSubmodule.gcomm_monoid
/-
/-- The weighted homogeneous submodules form a graded monoid. -/
instance WeightedHomogeneousSubmodule.gcomm_monoid {w : σ → M} :
    SetLike.GradedMonoid (weightedHomogeneousSubmodule R w)
    where
  one_mem := isWeightedHomogeneous_one R w
  mul_mem i j xi xj := IsWeightedHomogeneous.mul
#align mv_polynomial.is_weighted_homogeneous.weighted_homogeneous_submodule.gcomm_monoid MvPolynomial.IsWeightedHomogeneous.WeightedHomogeneousSubmodule.gcomm_monoid
-/

end IsWeightedHomogeneous

-- #print MvPolynomial.weightedHomogeneousComponent
/-
/-- `weighted_homogeneous_component w n φ` is the part of `φ` that is weighted homogeneous of
  weighted degree `n`, with respect to the weights `w`.
  See `sum_weighted_homogeneous_component` for the statement that `φ` is equal to the sum
  of all its weighted homogeneous components. -/
def weightedHomogeneousComponent (w : σ → M) (n : M) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (Submodule.subtype _).comp <| Finsupp.restrictDom _ _ {d | weightedDegree' w d = n}
#align mv_polynomial.weighted_homogeneous_component MvPolynomial.weightedHomogeneousComponent
-/

section WeightedHomogeneousComponent

variable {w : σ → M} (n : M) (φ ψ : MvPolynomial σ R)

variable {R}

-- #print MvPolynomial.coeff_weightedHomogeneousComponent
/-
-- MODIF : add [decidable_eq M]
theorem coeff_weightedHomogeneousComponent [DecidableEq M] (d : σ →₀ ℕ) :
    coeff d (weightedHomogeneousComponent R w n φ) =
      if weightedDegree' w d = n then coeff d φ else 0 :=
  Finsupp.filter_apply (fun d : σ →₀ ℕ => weightedDegree' w d = n) φ d
#align mv_polynomial.coeff_weighted_homogeneous_component MvPolynomial.coeff_weightedHomogeneousComponent
-/

-- #print MvPolynomial.weightedHomogeneousComponent_apply
/-
-- MODIF : add [decidable_eq M]
theorem weightedHomogeneousComponent_apply [DecidableEq M] :
    weightedHomogeneousComponent R w n φ =
      ∑ d in φ.support.filterₓ fun d => weightedDegree' w d = n, monomial d (coeff d φ) :=
  Finsupp.filter_eq_sum (fun d : σ →₀ ℕ => weightedDegree' w d = n) φ
#align mv_polynomial.weighted_homogeneous_component_apply MvPolynomial.weightedHomogeneousComponent_apply
-/

-- #print MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
/-
-- MODIF : add [decidable_eq M]
/-- The `n` weighted homogeneous component of a polynomial is weighted homogeneous of
weighted degree `n`. -/
theorem weightedHomogeneousComponent_isWeightedHomogeneous :
    (weightedHomogeneousComponent R w n φ).IsWeightedHomogeneous w n := by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weighted_homogeneous_component, if_neg hd]
#align mv_polynomial.weighted_homogeneous_component_is_weighted_homogeneous MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
-/

-- MODIF : new lemma
theorem weightedHomogeneousComponent_mem (w : σ → M) (φ : MvPolynomial σ R) (m : M) :
    weightedHomogeneousComponent w m φ ∈ weightedHomogeneousSubmodule R w m :=
  by
  rw [mem_weightedHomogeneousSubmodule]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ
#align mv_polynomial.weighted_homogeneous_component_mem MvPolynomial.weightedHomogeneousComponent_mem

-- #print MvPolynomial.weightedHomogeneousComponent_C_mul
/-
@[simp]
theorem weightedHomogeneousComponent_C_mul (n : M) (r : R) :
    weightedHomogeneousComponent R w n (C r * φ) = C r * weightedHomogeneousComponent R w n φ := by
  simp only [C_mul', LinearMap.map_smul]
#align mv_polynomial.weighted_homogeneous_component_C_mul MvPolynomial.weightedHomogeneousComponent_C_mul
-/

-- #print MvPolynomial.weightedHomogeneousComponent_eq_zero'
/-
theorem weightedHomogeneousComponent_eq_zero'
    (h : ∀ d : σ →₀ ℕ, d ∈ φ.support → weightedDegree' w d ≠ n) :
    weightedHomogeneousComponent R w n φ = 0 := by
  classical
  rw [weighted_homogeneous_component_apply, sum_eq_zero]
  intro d hd
  rw [mem_filter] at hd
  exfalso
  exact h _ hd.1 hd.2
#align mv_polynomial.weighted_homogeneous_component_eq_zero' MvPolynomial.weightedHomogeneousComponent_eq_zero'
-/

-- #print MvPolynomial.weightedHomogeneousComponent_eq_zero
/-
theorem weightedHomogeneousComponent_eq_zero [SemilatticeSup M] [OrderBot M]
    (h : weightedTotalDegree w φ < n) : weightedHomogeneousComponent R w n φ = 0 := by
  classical
  rw [weighted_homogeneous_component_apply, sum_eq_zero]
  intro d hd
  rw [mem_filter] at hd
  exfalso
  apply lt_irrefl n
  nth_rw 1 [← hd.2]
  exact lt_of_le_of_lt (le_weighted_total_degree w hd.1) h
#align mv_polynomial.weighted_homogeneous_component_eq_zero MvPolynomial.weightedHomogeneousComponent_eq_zero
-/

variable (w)

-- #print MvPolynomial.weightedHomogeneousComponent_finsupp
/-
theorem weightedHomogeneousComponent_finsupp :
    (Function.support fun m => weightedHomogeneousComponent R w m φ).Finite :=
  by
  suffices
    (Function.support fun m => weighted_homogeneous_component R w m φ) ⊆
      (fun d => weighted_degree' w d) '' φ.support
    by
    exact finite.subset ((fun d : σ →₀ ℕ => (weighted_degree' w) d) '' ↑(support φ)).toFinite this
  intro m hm
  by_contra hm'; apply hm
  simp only [mem_support, Ne.def] at hm
  simp only [Set.mem_image, not_exists, not_and] at hm'
  exact weighted_homogeneous_component_eq_zero' m φ hm'
#align mv_polynomial.weighted_homogeneous_component_finsupp MvPolynomial.weightedHomogeneousComponent_finsupp
-/

-- variable (w)

-- #print MvPolynomial.sum_weightedHomogeneousComponent
/-
/-- Every polynomial is the sum of its weighted homogeneous components. -/
theorem sum_weightedHomogeneousComponent :
    ((weightedHomogeneousComponent_finsupp w φ).toFinset.Sum fun m =>
        weightedHomogeneousComponent R w m φ) =
      φ :=
  by
  classical
  ext1 d
  simp only [coeff_sum, coeff_weighted_homogeneous_component]
  rw [Finset.sum_eq_single (weighted_degree' w d)]
  · rw [if_pos rfl]
  · intro m hm hm'; rw [if_neg hm'.symm]
  · intro hm; rw [if_pos rfl]
    simp only [finite.mem_to_finset, mem_support, Ne.def, Classical.not_not] at hm
    have := coeff_weighted_homogeneous_component (_ : M) φ d
    rw [hm, if_pos rfl, coeff_zero] at this
    exact this.symm
#align mv_polynomial.sum_weighted_homogeneous_component MvPolynomial.sum_weightedHomogeneousComponent
-/

/- -- Useless
theorem finsum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ :=
  -- rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  sum_weightedHomogeneousComponent _ _
#align mv_polynomial.finsum_weighted_homogeneous_component MvPolynomial.finsum_weightedHomogeneousComponent
-/

variable {w}

-- MODIF : new lemma
theorem weightedHomogeneousComponent_of_weighted_homogeneous_polynomial_same
    [DecidableEq M]
    (m : M) (p : MvPolynomial σ R) (hp : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
--   classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    rfl; rw [zero_coeff]
  · rw [hp zero_coeff, if_pos]; rfl
#align mv_polynomial.weighted_homogeneous_component_of_weighted_homogeneous_polynomial_same MvPolynomial.weightedHomogeneousComponent_of_weighted_homogeneous_polynomial_same

-- MODIF : new lemma
theorem weightedHomogeneousComponent_of_weightedHomogeneous_ne
    [DecidableEq M]
    (m n : M) (p : MvPolynomial σ R) (hp : IsWeightedHomogeneous w p m) :
    n ≠ m → weightedHomogeneousComponent w n p = 0 := by
--  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    rw [zero_coeff]; rw [coeff_zero]; rw [coeff_zero]
  · rw [if_neg]; rw [coeff_zero]; rw [hp zero_coeff]; exact Ne.symm hn
#align mv_polynomial.weighted_homogeneous_component_of_weighted_homogeneous_polynomial_other MvPolynomial.weightedHomogeneousComponent_of_weightedHomogeneous_ne

-- #print MvPolynomial.weightedHomogeneousComponent_weighted_homogeneous_polynomial
/-
-- MODIF : add [decidable_eq M]
/-- The weighted homogeneous components of a weighted homogeneous polynomial. -/
theorem weightedHomogeneousComponent_weighted_homogeneous_polynomial [DecidableEq M] (m n : M)
    (p : MvPolynomial σ R) (hp : p ∈ weightedHomogeneousSubmodule R w n) :
    weightedHomogeneousComponent R w m p = if m = n then p else 0 :=
  by
  rw [mem_weighted_homogeneous_submodule] at hp
  split_ifs
  rw [h]
  exact weighted_homogeneous_component_of_weighted_homogeneous_polynomial_same n p hp
  exact weighted_homogeneous_component_of_weighted_homogeneous_polynomial_other n m p hp h
#align mv_polynomial.weighted_homogeneous_component_weighted_homogeneous_polynomial MvPolynomial.weightedHomogeneousComponent_weighted_homogeneous_polynomial
-/

variable (R w)

-- MODIF : new lemma
-- Rewrite direct_sum.coe_linear_map
theorem DirectSum.coeLinearMap_eq_support_sum
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) :=
  by rw [DirectSum.coeLinearMap_eq_dfinsupp_sum]
#align mv_polynomial.direct_sum.coe_linear_map_eq_support_sum MvPolynomial.DirectSum.coeLinearMap_eq_support_sum

-- MODIF : new lemma
-- Rewrite direct_sum.coe_add_monoid_hom
theorem DirectSum.coeAddMonoidHom_eq_support_sum
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) :=
  DirectSum.coeLinearMap_eq_support_sum R w x
#align mv_polynomial.direct_sum.coe_add_monoid_hom_eq_support_sum MvPolynomial.DirectSum.coeAddMonoidHom_eq_support_sum

-- MODIF : new lemma
-- Variants for finsum
theorem DirectSum.coeLinearMap_eq_finsum
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m := by
  -- classical
  rw [DirectSum.coeLinearMap_eq_support_sum, DFinsupp.sum]
  rw [finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset_submodule
#align mv_polynomial.direct_sum.coe_linear_map_eq_finsum MvPolynomial.DirectSum.coeLinearMap_eq_finsum

-- MODIF : new lemma
theorem DirectSum.coeAddMonoidHom_eq_finsum
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m :=
  DirectSum.coeLinearMap_eq_finsum R w x
#align mv_polynomial.direct_sum.coe_add_monoid_hom_eq_finsum MvPolynomial.DirectSum.coeAddMonoidHom_eq_finsum

-- MODIF : new lemma
theorem weightedHomogeneousComponent_weightedHomogeneousPolynomial'
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (m : M) (x : weightedHomogeneousSubmodule R w m) :
  (weightedHomogeneousComponent w m) ↑x = (x : MvPolynomial σ R) := by
  -- classical
  rw [weightedHomogeneousComponent_weighted_homogeneous_polynomial m m _ x.prop,
    if_pos rfl]
#align mv_polynomial.weighted_homogeneous_component_weighted_homogeneous_polynomial' MvPolynomial.weightedHomogeneousComponent_weightedHomogeneousPolynomial'

-- MODIF : new lemma
theorem weightedHomogeneousComponent_directSum
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) (m : M) :
    (weightedHomogeneousComponent w m)
        ((DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x) =
      x m := by
  rw [DirectSum.coeLinearMap_eq_dfinsupp_sum, DFinsupp.sum, map_sum]
  convert @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [weightedHomogeneousComponent_of_weighted_homogeneous_polynomial_same]
    rw [← mem_weightedHomogeneousSubmodule]
    exact (x m).prop
  · intro n _ hmn
    rw [weightedHomogeneousComponent_of_weightedHomogeneous_ne n m]
    rw [← mem_weightedHomogeneousSubmodule]
    exact (x n).prop
    exact Ne.symm hmn
  · rw [DFinsupp.not_mem_support_iff]
    intro hm; rw [hm, Submodule.coe_zero, map_zero]
#align mv_polynomial.weighted_homogeneous_component_direct_sum MvPolynomial.weightedHomogeneousComponent_directSum

end WeightedHomogeneousComponent

end AddCommMonoid

section CanonicallyOrderedAddMonoid

variable
  [CanonicallyOrderedAddCommMonoid M]
  {w : σ → M} (φ : MvPolynomial σ R)

-- MODIF : new definition and new lemma
/-- A weight function is nontrivial if its values are not torsion -/
def NonTorsionWeight (w : σ → M) :=
  ∀ n x, n • w x = (0 : M) → n = 0
#align mv_polynomial.non_trivial_weight MvPolynomial.NonTorsionWeight

theorem nonTorsionWeight_of_nonZero [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) : NonTorsionWeight w := by
  intro n x; rw [smul_eq_zero]
  intro hnx
  cases' hnx with hn hx
  exact hn
  exfalso; exact hw x hx
#align mv_polynomial.non_trivial_weight_of MvPolynomial.nonTorsionWeight_of_nonZero

-- #print MvPolynomial.weightedHomogeneousComponent_zero
/-
-- MODIF : generalize for non_trivial_weight
/-- If `M` is a `canonically_ordered_add_monoid`,
  then the `weighted_homogeneous_component` of weighted degree `0`
  of a polynomial is its constant coefficient. -/
@[simp]
theorem weightedHomogeneousComponent_zero' (hw : NonTorsionWeight w) :
    weightedHomogeneousComponent w 0 φ = C (coeff 0 φ) := by
  classical
  ext1 d
  rcases em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    rw [weightedDegree', Finsupp.total_apply, Finsupp.sum, sum_eq_zero_iff]
    intro h
    apply hd
    ext x; simp only [Finsupp.coe_zero, Pi.zero_apply]
    specialize h x
    by_contra hx
    rw [Finsupp.mem_support_iff] at h
    exact hx (hw (d x) x (h hx))
#align mv_polynomial.weighted_homogeneous_component_zero' MvPolynomial.weightedHomogeneousComponent_zero'
-/

end CanonicallyOrderedAddMonoid

section CanonicallyLinearOrderedMonoid

variable [CanonicallyLinearOrderedAddCommMonoid M] {w : σ → M} (φ : MvPolynomial σ R)

example (p q : Prop) : ((¬ p → q) ↔ p) ↔ (q → p) :=  by
  by_cases hp : p
  · simp [hp]
  · simp [hp]

-- MODIF : generalize to non_trivial_weight
theorem weightedDegree'_eq_zero_iff (hw : NonTorsionWeight w) (m : σ →₀ ℕ) :
    weightedDegree' w m = 0 ↔ ∀ x : σ, m x = 0 := by
  simp only [weightedDegree', Finsupp.total]
  simp only [LinearMap.toAddMonoidHom_coe, coe_lsum, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  rw [Finsupp.sum, Finset.sum_eq_zero_iff]
  apply forall_congr'; intro x
  rw [Finsupp.mem_support_iff]
  simp only [ne_eq]
  by_cases hx : m x = 0
  · simp only [hx, not_true_eq_false, zero_smul, IsEmpty.forall_iff]
  · simp only [hx, not_false_eq_true, forall_true_left, iff_false]
    exact fun hx' => hx (hw _ _ hx')
#align mv_polynomial.weighted_degree'_eq_zero_iff MvPolynomial.weightedDegree'_eq_zero_iff

-- MODIF : new lemma
theorem isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = 0 := by
  rw [weightedTotalDegree, ← bot_eq_zero, Finset.sup_eq_bot_iff, bot_eq_zero, IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]
#align mv_polynomial.is_weighted_homogeneous_of_total_weighted_degree_zero_iff
  MvPolynomial.isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero

-- MODIF : new lemma
theorem weightedTotalDegree_eq_zero_iff (hw : NonTorsionWeight w) (p : MvPolynomial σ R) :
    p.weightedTotalDegree w = 0 ↔ ∀ (m : σ →₀ ℕ) (_ : m ∈ p.support) (x : σ), m x = ⊥ :=
  by
  rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, IsWeightedHomogeneous]
  apply forall_congr'; intro m
  rw [mem_support_iff]
  apply forall_congr'; intro hm
  simp only [bot_eq_zero']
  exact weightedDegree'_eq_zero_iff hw m
#align mv_polynomial.weighted_total_degree_eq_zero_iff MvPolynomial.weightedTotalDegree_eq_zero_iff

end CanonicallyLinearOrderedMonoid

-- MODIF : new section
section GradedAlgebra

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the
  ring of multivariate polynomials `mv_polynomial σ R` with the structure of a graded algebra -/
variable (w : σ → M) [AddCommMonoid M]

/- instance [DecidableEq σ] [DecidableEq R] :
    ∀ (i : M) (x : ↥(weightedHomogeneousSubmodule R w i)), Decidable (x ≠ 0) :=
  by
  intro m x
  rw [Ne.def, ← SetLike.coe_eq_coe]
  infer_instance -/

-- variable [DecidableEq σ] [DecidableEq R] [DecidableEq M]

private theorem decompose'_aux
    [DecidableEq M]
    (φ : MvPolynomial σ R) (i : M) (hi : i ∉ Finset.image (weightedDegree' w) φ.support) :
    weightedHomogeneousComponent w i φ = 0 :=
  by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, Ne.def, exists_prop, not_exists, not_and] at hi
  intro m hm
  apply hi m
  rw [mem_support_iff] at hm
  exact hm

variable (R)

private def decompose'_toFun [DecidableEq M] := fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weightedDegree' w) φ.support) fun m =>
    ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩

private theorem decompose'_toFun_apply [DecidableEq M] (φ : MvPolynomial σ R) (m : M) :
    (decompose'_toFun R w φ m : MvPolynomial σ R) = weightedHomogeneousComponent w m φ :=
  by
  rw [decompose'_toFun]
  by_cases hm : m ∈ Finset.image (weightedDegree' w) φ.support
  simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  rw [DirectSum.mk_apply_of_not_mem hm, Submodule.coe_zero, decompose'_aux w φ m hm]

/- instance [decidable_eq σ] [decidable_eq R] :
  Π (i : M) (x : ↥(weighted_homogeneous_submodule R w i)), decidable (x ≠ 0) :=
begin
  intros m x,
  rw [ne.def, ← set_like.coe_eq_coe],
  apply_instance,
end -/
/-- Given a weight w, the decomposition of mv_polynomial σ R into weighted homogeneous submodules -/
def weightedDecomposition [DecidableEq σ] [DecidableEq R] [DecidableEq M] :
  DirectSum.Decomposition (weightedHomogeneousSubmodule R w) where
  decompose' := decompose'_toFun R w
  left_inv φ := by
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (fun m => ↥(weightedHomogeneousSubmodule R w m))
        (decompose'_toFun R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, MvPolynomial.coeff_sum, map_sum]
    rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.sum_congr
    · ext m
      simp only [DFinsupp.mem_support_toFun, Ne.def, Set.Finite.mem_toFinset, Function.mem_support,
        not_iff_not]
      conv_lhs => rw [← Subtype.coe_inj]
      rw [decompose'_toFun_apply, Submodule.coe_zero]
    · intro m _
      rw [decompose'_toFun_apply]
  right_inv x := by
    apply DFinsupp.ext; intro m
    rw [← Subtype.coe_inj]
    rw [decompose'_toFun_apply]
    apply weightedHomogeneousComponent_directSum
#align mv_polynomial.weighted_decomposition MvPolynomial.weightedDecomposition

/-- Given a weight, mv_polynomial as a graded algebra -/
def weightedGradedAlgebra [DecidableEq σ] [DecidableEq R] [DecidableEq M] :
  GradedAlgebra (weightedHomogeneousSubmodule R w) where
  toDecomposition := weightedDecomposition R w
  toGradedMonoid := inferInstance
#align mv_polynomial.weighted_graded_algebra MvPolynomial.weightedGradedAlgebra

theorem weightedDecomposition.decompose'_eq
    [DecidableEq σ] [DecidableEq R] [DecidableEq M] :
  (weightedDecomposition R w).decompose' = fun φ : MvPolynomial σ R =>
    DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
      (Finset.image (weightedDegree' w) φ.support) fun m =>
        ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩ :=
  rfl
#align mv_polynomial.weighted_decomposition.decompose'_eq MvPolynomial.weightedDecomposition.decompose'_eq

theorem weightedDecomposition.decompose'_apply
    [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (φ : MvPolynomial σ R) (m : M) :
  ((weightedDecomposition R w).decompose' φ m : MvPolynomial σ R) =
    weightedHomogeneousComponent w m φ :=
  decompose'_toFun_apply R w φ m
#align mv_polynomial.weighted_decomposition.decompose'_apply MvPolynomial.weightedDecomposition.decompose'_apply

end GradedAlgebra

end MvPolynomial

--#lint
