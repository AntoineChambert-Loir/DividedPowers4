import Mathlib.RingTheory.TensorProduct.Basic

namespace LinearForm

open Algebra Algebra.TensorProduct Function LinearMap TensorProduct

variable (R S S' M : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring S']
  [Algebra R S'] (φ : S →ₐ[R] S') [AddCommMonoid M] [Module R M]

noncomputable def baseChange (f : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (Algebra.TensorProduct.rid R S S).toLinearMap.comp (f.baseChange S)

theorem baseChange_apply_tmul (f : M →ₗ[R] R) (r : S) (m : M) :
    baseChange R S M f (r ⊗ₜ[R] m) = r * ((f m) • (1 : S)) := by
  simp [baseChange, coe_comp, Function.comp_apply, baseChange_tmul, AlgEquiv.toLinearMap_apply,
    rid_tmul, Algebra.mul_smul_comm, mul_one]

-- Mathlib.RingTheory.TensorProduct.Basic
theorem baseChange_compat_apply (f : M →ₗ[R] R) (m : S ⊗[R] M) :
    φ (baseChange R S M f m) = (baseChange R S' M f) ((rTensor M φ.toLinearMap) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul => simp [baseChange, coe_comp, Function.comp_apply, baseChange_tmul,
      AlgEquiv.toLinearMap_apply, rid_tmul, map_smul, rTensor_tmul, AlgHom.toLinearMap_apply]
  | add x y hx hy => simp [map_add, hx, hy]

end LinearForm
