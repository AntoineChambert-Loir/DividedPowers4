import DividedPowers.ForMathlib.Algebra.Algebra.Bilinear --required for the last two lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Pi --required for the last lemma
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open LinearMap TensorProduct

variable {R σ M N : Type*} [CommSemiring R] [DecidableEq σ] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
namespace MvPolynomial

theorem rTensor_lcoeff (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    (LinearMap.rTensor N (lcoeff R k)) sn = 1 ⊗ₜ[R] (scalarRTensor sn) k  := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    simp only [rTensor_tmul, scalarRTensor_apply_tmul, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single k (fun b _ hb ↦ by rw [Finsupp.single_eq_of_ne hb.symm])
      (fun _ ↦ by rw [_root_.zero_smul, Finsupp.single_zero, Finsupp.coe_zero, Pi.zero_apply]),
      Finsupp.single_eq_same, lcoeff_apply, ← smul_tmul, smul_eq_mul, mul_one]
    congr
  | add x y hx hy => simp [LinearMap.map_add, LinearEquiv.map_add, hx, hy,
      Finsupp.add_apply, tmul_add]

theorem scalarRTensor_apply (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    scalarRTensor sn k = TensorProduct.lid R N ((LinearMap.rTensor N (lcoeff R k)) sn) := by
  rw [← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply, rTensor_lcoeff]

end MvPolynomial

open MvPolynomial

theorem LinearMap.rTensor_finsuppLeft_eq {S S' : Type*} [CommSemiring S] [Algebra R S]
    [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') (k : σ →₀ ℕ) (sn : MvPolynomial σ S ⊗[R] N) :
    (LinearMap.rTensor N φ.toLinearMap) (((finsuppLeft R S N (σ →₀ ℕ)) sn) k) =
      ((finsuppLeft R S' N (σ →₀ ℕ)) ((LinearMap.rTensor N (mapAlgHom φ).toLinearMap) sn)) k := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | tmul p n =>
    rw [rTensor_tmul, finsuppLeft_apply_tmul_apply,
      rTensor_tmul, finsuppLeft_apply_tmul_apply]
    congr
    exact (MvPolynomial.coeff_map φ.toRingHom p k).symm
  | add x y hx hy => simp [← hx, ← hy]

theorem TensorProduct.finsuppLeft_symm_apply_eq_sum {S : Type*} [CommSemiring S] [Algebra R S]
    (sn : (σ →₀ ℕ) →₀ S ⊗[R] N) : (finsuppLeft R S N (σ →₀ ℕ)).symm sn =
      sn.sum fun k ↦ ⇑(AlgebraTensorModule.map (monomial k) LinearMap.id) := by
  induction sn using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [Finsupp.sum_add_index (by simp) (by simp), ← hx, ← hy, map_add]
  | single k x =>
    simp only [map_zero, Finsupp.sum_single_index]
    induction x using TensorProduct.induction_on with
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul s n =>
      simp [finsuppLeft_symm_apply_single, single_eq_monomial]
    | zero => simp

open Finsupp MvPolynomial TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)] {S : Type*} [CommSemiring S] [Algebra R S] (s : S) (m : Π i, M i)

theorem TensorProduct.tmul_eq_aeval_one_sum :
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

theorem TensorProduct.eq_rTensor_sum (sm : S ⊗[R] ((i : ι) → M i)) :
    sm = (LinearMap.rTensor ((i : ι) → M i) (AlgHom.restrictScalars R (aeval 1)).toLinearMap)
      (∑ j, (LinearEquiv.rTensor ((i : ι) → M i) (scalarRTensorAlgEquiv (R := R)).toLinearEquiv)
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
