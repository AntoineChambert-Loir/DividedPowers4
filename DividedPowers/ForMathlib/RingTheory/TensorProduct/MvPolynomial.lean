import Mathlib.RingTheory.TensorProduct.MvPolynomial

open LinearMap TensorProduct

variable {R σ M N ι : Type*} [CommSemiring R] [DecidableEq σ] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
namespace MvPolynomial

theorem rTensor_lcoeff (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    (LinearMap.rTensor N (lcoeff R k)) sn = 1 ⊗ₜ[R] (scalarRTensor sn) k  := by
  induction sn using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    simp only [rTensor_tmul, scalarRTensor_apply_tmul, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single k (fun b _ hb ↦ by rw [Finsupp.single_eq_of_ne hb])
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
