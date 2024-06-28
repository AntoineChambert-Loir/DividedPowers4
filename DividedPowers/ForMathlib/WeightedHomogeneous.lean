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

open scoped BigOperators

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type _} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type _}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weighted_degree'` -/


section WeightedHomogeneousComponent

variable {w : σ → M} (n : M) (φ ψ : MvPolynomial σ R)

--431
theorem weightedHomogeneousComponent_of_weighted_homogeneous_polynomial_same
    (m : M) (p : MvPolynomial σ R) (hp : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    rfl; rw [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]

theorem weightedHomogeneousComponent_of_weightedHomogeneous_ne
    (m n : M) (p : MvPolynomial σ R) (hp : IsWeightedHomogeneous w p m) :
    n ≠ m → weightedHomogeneousComponent w n p = 0 := by
  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs <;> simp only [zero_coeff, coeff_zero]
  · rw [if_neg (by simp only [hp zero_coeff, hn.symm, not_false_eq_true]), coeff_zero]

variable (R w)

theorem DirectSum.coeLinearMap_eq_support_sum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) := by
  rw [DirectSum.coeLinearMap_eq_dfinsupp_sum]

theorem DirectSum.coeAddMonoidHom_eq_support_sum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) :=
  DirectSum.coeLinearMap_eq_support_sum R w x

theorem DirectSum.coeLinearMap_eq_finsum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m := by
  rw [DirectSum.coeLinearMap_eq_support_sum, DFinsupp.sum, finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset_submodule

theorem DirectSum.coeAddMonoidHom_eq_finsum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m :=
  DirectSum.coeLinearMap_eq_finsum R w x

-- TODO: we have deleted a ' in the name (check this is no problem)
-- TODO: rename weightedHomogeneousComponent_weighted_homogeneous_polynomial in Mathlib
theorem weightedHomogeneousComponent_weightedHomogeneousPolynomial
    (m : M) (x : weightedHomogeneousSubmodule R w m) :
  (weightedHomogeneousComponent w m) ↑x = (x : MvPolynomial σ R) := by
   classical
  rw [weightedHomogeneousComponent_weighted_homogeneous_polynomial m m _ x.prop, if_pos rfl]

theorem weightedHomogeneousComponent_directSum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) (m : M) :
    (weightedHomogeneousComponent w m)
      ((DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x) = x m := by
  rw [DirectSum.coeLinearMap_eq_dfinsupp_sum, DFinsupp.sum, map_sum]
  convert @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [weightedHomogeneousComponent_of_weighted_homogeneous_polynomial_same _ _ (x m).prop]
  · intro n _ hmn
    rw [weightedHomogeneousComponent_of_weightedHomogeneous_ne n m _ (x n).prop hmn.symm]
  · rw [DFinsupp.not_mem_support_iff]
    intro hm; rw [hm, Submodule.coe_zero, map_zero]

end WeightedHomogeneousComponent

end AddCommMonoid

section CanonicallyOrderedAddMonoid

variable [CanonicallyOrderedAddCommMonoid M] {w : σ → M} (φ : MvPolynomial σ R)

-- 520  (TODO: Search for nonTorsionWeight)
theorem nonTorsionWeight_of_nonZero [NoZeroSMulDivisors ℕ M] (hw : ∀ i : σ, w i ≠ 0) :
    NonTorsionWeight w := fun _ x hnx ↦ Or.resolve_right (smul_eq_zero.mp hnx) (hw x)

end CanonicallyOrderedAddMonoid

section GradedAlgebra

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the
  ring of multivariate polynomials `mv_polynomial σ R` with the structure of a graded algebra -/
variable (w : σ → M) [AddCommMonoid M]

theorem weightedHomogeneousComponent_eq_zero_of_not_mem [DecidableEq M]
    (φ : MvPolynomial σ R) (i : M) (hi : i ∉ Finset.image (weightedDegree w) φ.support) :
    weightedHomogeneousComponent w i φ = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, ne_eq, exists_prop, not_exists, not_and] at hi
  exact fun m hm ↦ hi m (mem_support_iff.mp hm)

variable (R)

#check DirectSum.mk_apply_of_mem

/-- The `decompose'` argument of `weightedDecomposition`.  -/
def decompose' [DecidableEq M] := fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weightedDegree w) φ.support) fun m =>
      ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩

theorem decompose'_apply [DecidableEq M] (φ : MvPolynomial σ R) (m : M) :
    (decompose' R w φ m : MvPolynomial σ R) = weightedHomogeneousComponent w m φ := by
  rw [decompose']
  by_cases hm : m ∈ Finset.image (weightedDegree w) φ.support
  simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  rw [DirectSum.mk_apply_of_not_mem hm, Submodule.coe_zero,
    weightedHomogeneousComponent_eq_zero_of_not_mem w φ m hm]

/-- Given a weight w, the decomposition of mv_polynomial σ R into weighted homogeneous submodules -/
def weightedDecomposition /- [DecidableEq σ] [DecidableEq R]-/ [DecidableEq M] :
  DirectSum.Decomposition (weightedHomogeneousSubmodule R w) where
  decompose' := decompose' R w
  left_inv φ := by
    classical
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (fun m => ↥(weightedHomogeneousSubmodule R w m))
        (decompose' R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, MvPolynomial.coeff_sum, map_sum,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.sum_congr _ (fun m _ ↦ by rw [decompose'_apply])
    ext m
    simp only [DFinsupp.mem_support_toFun, ne_eq, Set.Finite.mem_toFinset, Function.mem_support,
      not_iff_not]
    conv_lhs => rw [← Subtype.coe_inj]
    rw [decompose'_apply, Submodule.coe_zero]
  right_inv x := by
    classical
    apply DFinsupp.ext
    intro m
    rw [← Subtype.coe_inj, decompose'_apply]
    exact weightedHomogeneousComponent_directSum R w x m

/-- Given a weight, `MvPolynomial` as a graded algebra -/
def weightedGradedAlgebra /- [DecidableEq σ] [DecidableEq R] -/ [DecidableEq M] :
    GradedAlgebra (weightedHomogeneousSubmodule R w) where
  toDecomposition := weightedDecomposition R w
  toGradedMonoid  := inferInstance

theorem weightedDecomposition.decompose'_eq [DecidableEq σ] [DecidableEq R] [DecidableEq M] :
  (weightedDecomposition R w).decompose' = fun φ : MvPolynomial σ R =>
    DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
      (Finset.image (weightedDegree w) φ.support) fun m =>
        ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩ := rfl

theorem weightedDecomposition.decompose'_apply [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (φ : MvPolynomial σ R) (m : M) :
    ((weightedDecomposition R w).decompose' φ m : MvPolynomial σ R) =
      weightedHomogeneousComponent w m φ :=
  MvPolynomial.decompose'_apply R w φ m

end GradedAlgebra

end MvPolynomial
