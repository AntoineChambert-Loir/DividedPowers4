/- Copyright ACL & MIdFF 2025 -/

import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section

namespace TensorProduct

/- **MI** : I think that `TensorProduct.piRight_apply` should not be a simp lemma, and that we
should stick to `piRight` as often as possible (TODO: PR this change). -/

variable {ι R S T N P : Type*} {M : ι → Type*}  /- [Fintype ι] [DecidableEq ι] -/ [CommSemiring R]
    [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)] [CommSemiring S] [Algebra R S]
    [CommSemiring T] [Algebra R T] [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]

lemma piRightHom_rTensor_eq_rTensor_piRightHom (ψ : N →ₗ[R] P) (m : N ⊗[R] (Π i, M i)) (i : ι) :
    (piRightHom R S P M) ((LinearMap.rTensor (Π i, M i) ψ) m) i =
      LinearMap.rTensor (M i) ψ (piRightHom R S N M m i) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply] at hx hy ⊢
    rw [hx, hy]
  | tmul t m => simp

lemma piRight_rTensor_eq_rTensor_piRight [Fintype ι] [DecidableEq ι] (ψ : N →ₗ[R] P)
    (m : N ⊗[R] (Π i, M i)) :
    (piRight R S P M) ((LinearMap.rTensor (Π i, M i) ψ) m) =
      fun i ↦ LinearMap.rTensor (M i) ψ (piRight R S N M m i) := by
  ext i
  simp [piRightHom_rTensor_eq_rTensor_piRightHom]

variable (R S N)

@[simp]
lemma coe_piRightHom : ⇑(piRightHom R S N M) = (piRightHom R R N M) := rfl

@[simp]
lemma coe_piRight [Fintype ι] [DecidableEq ι] : ⇑(piRight R S N M) = (piRight R R N M) := rfl

@[simp]
lemma coe_piRight_symm [Fintype ι] [DecidableEq ι] :
    ⇑(piRight R S N M).symm = (piRight R R N M).symm := by
  ext d
  simp only [LinearEquiv.symm_apply_eq, coe_piRight, LinearEquiv.apply_symm_apply]

-- I tried to avoid the next one, but with no success (TODO)
lemma piRight_rTensor_eq_rTensor_piRight'
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommSemiring R]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {T : Type*} [CommSemiring T] [Algebra R T]
    (ψ : T →ₐ[R] S)
    (m : T ⊗[R] ((i : ι) → M i)) (i : ι) :
    (piRight R S S M) ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap) m) i =
      LinearMap.rTensor (M i) ψ.toLinearMap (piRight R T T M m i) := by
  simp [piRightHom_rTensor_eq_rTensor_piRightHom]

variable {R S N} [Fintype ι] [DecidableEq ι]

lemma piRight_symm_zero :
    ((piRight R S N M).symm fun _ ↦ 0) = 0 := by
  rw [← Pi.zero_def, map_zero]

lemma piRight_apply_symm_zero :
    (piRight R S N M) ((piRight R S N M).symm fun _ ↦ 0) = 0 := by
  rw [piRight_symm_zero, map_zero]

lemma smul_tmul_proj_eq (r' : ι → S) (i : ι) (s : S) (m : Π i, M i) :
    r' i • s ⊗ₜ[R] m i = (piRight R S S M)
      (r' i • s ⊗ₜ[R] Pi.single i (m i)) i := by simp

theorem smul_piRight_apply (sm : S ⊗[R] (Π i, M i)) (r' : ι → S) (i : ι) :
    r' i • (piRight R S S M) sm i =
      (piRight R S S M) ((piRight R S S M).symm fun i ↦ r' i • (piRight R S S M) sm i) i := by
  rw [← Pi.smul_apply, ← map_smul]
  induction sm using TensorProduct.induction_on with
  | zero =>
    simp only [smul_zero, map_zero, Pi.zero_apply, piRight_symm_zero]
  | add x y hx hy =>
    simp only [smul_add, hx, hy, coe_piRight_symm,← Pi.add_def, map_add, Pi.add_apply]
  | tmul s m =>
    simp only [map_smul, piRight_apply, piRightHom_tmul, Pi.smul_apply, coe_piRight_symm,
      coe_piRightHom]
    rw [← piRight_apply, smul_tmul_proj_eq]
    simp

end TensorProduct
