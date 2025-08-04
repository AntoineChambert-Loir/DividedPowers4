import Mathlib.RingTheory.TensorProduct.MvPolynomial

namespace MvPolynomial

variable {R σ M N ι : Type*} [CommSemiring R] [DecidableEq σ] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

open LinearMap TensorProduct

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

-- Mathlib.RingTheory.TensorProduct.MvPolynomial
theorem scalarRTensor_apply (sn : MvPolynomial σ R ⊗[R] N) (k : σ →₀ ℕ) :
    scalarRTensor sn k = TensorProduct.lid R N ((LinearMap.rTensor N (lcoeff R k)) sn) := by
  rw [← LinearEquiv.symm_apply_eq, TensorProduct.lid_symm_apply, rTensor_lcoeff]

end MvPolynomial
