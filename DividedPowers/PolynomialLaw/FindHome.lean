import DividedPowers.ForMathlib.Algebra.MvPolynomial.Lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Basic
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Pi
import DividedPowers.ForMathlib.Algebra.Algebra.Bilinear --required for the last two lemmas

--import DividedPowers.PolynomialLaw.Coeff

universe u

open Finsupp LinearMap MvPolynomial TensorProduct

variable {ι : Type*} {R : Type u} [CommSemiring R] {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N] {S : Type*} [CommSemiring S] [Algebra R S] [Fintype ι] [DecidableEq ι]
  (s : Π (_ : ι), S) (m : Π i, M i)

-- TODO: move
theorem tmul_eq_aeval_one_sum (S : Type*) [CommSemiring S] [Algebra R S] (s : S) :
    s ⊗ₜ[R] m = ∑ i, (aeval 1) (scalarRTensorAlgEquiv (X i ⊗ₜ[R] s)) ⊗ₜ[R] Pi.single i (m i) := by
  have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
  by_cases hR : Nontrivial R
  · conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply, rTensorAlgHom_apply_eq, aeval_def, Algebra.algebraMap_self, eval₂_map,
      RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul, Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    rw [finsupp_support_eq_support, support_X (R := R)]
    simp only [Finset.sum_singleton, map_zero, Finsupp.prod_single_index, mul_one,
      Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]
    simp [X, ← single_eq_monomial, single_eq_same]
  · have hSM := TensorProduct.not_nontrivial_of_not_nontrivial R S (Π i, M i)
      (Algebra.not_nontrivial_of_not_nontrivial R S hR)
    simp only [nontrivial_iff, ne_eq, not_exists, not_not] at hSM
    apply hSM

theorem extracted_1_1 {ι R S : Type*}
  [CommSemiring R] {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)]
  [(i : ι) → Module R (M i)]
  [Fintype ι] [DecidableEq ι] [CommSemiring S] [Algebra R S]
  (sm : S ⊗[R] ((i : ι) → M i)) :
  sm =
    (LinearMap.rTensor ((i : ι) → M i) (AlgHom.restrictScalars R (aeval 1)).toLinearMap)
      (∑ j,
        (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X j ⊗ₜ[R] (TensorProduct.compRight R S S M j) sm))) := by
  simp only [map_sum, LinearMap.rTensor]
  induction sm using TensorProduct.induction_on with
  | zero =>  simp [map_zero, tmul_zero, Finset.sum_const_zero]
  | tmul s m =>
    simp only [compRight_tmul, singleRight_tmul, assoc_symm_tmul, LinearEquiv.rTensor_tmul,
      AlgEquiv.toLinearEquiv_apply, map_tmul, AlgHom.toLinearMap_apply,
      AlgHom.coe_restrictScalars', id_coe, id_eq]
    apply tmul_eq_aeval_one_sum
  | add sm₁ sm₂ hsm₁ hsm₂ => simp [map_add, tmul_add, Finset.sum_add_distrib, ← hsm₁, ← hsm₂]

#find_home! extracted_1_1
