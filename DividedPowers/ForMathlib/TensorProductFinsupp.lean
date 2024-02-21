import Mathlib.RingTheory.TensorProduct
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff

open TensorProduct LinearMap

open scoped TensorProduct

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section

variable {ι : Type*} [DecidableEq ι]

noncomputable def Finsupp.tensorProductLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  LinearEquiv.ofLinear
    (TensorProduct.lift
      (Finsupp.lsum R (fun (i : ι) ↦ TensorProduct.curry (Finsupp.lsingle i))))
    (Finsupp.lsum R (fun i ↦ rTensor N (Finsupp.lsingle i)))
    (by ext i m n j; simp [Finsupp.lsum])
    (by ext i m n; simp [Finsupp.lsum])

lemma Finsupp.tensorProductLeft_apply_tmul (p : ι →₀ M) (n : N) :
  Finsupp.tensorProductLeft (p ⊗ₜ[R] n) =
    p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp [tensorProductLeft, Finsupp.lsum]

lemma Finsupp.tensorProductLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    Finsupp.tensorProductLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [Finsupp.tensorProductLeft, Finsupp.lsum]

noncomputable def Finsupp.tensorProductRight :
    M ⊗[R] (ι →₀ N) ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  ((TensorProduct.comm R _ _).trans
    (Finsupp.tensorProductLeft (ι := ι) (M := N) (N := M) (R := R))).trans
      (Finsupp.mapRange.linearEquiv (TensorProduct.comm R _ _))

variable {S : Type*} [CommSemiring S] [Algebra R S]
  [Module S M] [IsScalarTower R S M]

noncomputable def Finsupp.tensorProductLeft' :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ (M ⊗[R] N) := {
  Finsupp.tensorProductLeft with
  map_smul' := fun r t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply] at hx hy ⊢
      simp only [smul_add, map_add, hx, hy]
    | tmul p n =>
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply]
      simp only [TensorProduct.smul_tmul', tensorProductLeft_apply_tmul]
      rw [Finsupp.smul_sum]
      simp only [smul_single]
      -- fails : -- rw [Finsupp.sum_smul_index]
      apply symm
      rw [Finsupp.sum, Finsupp.sum_of_support_subset]
      apply Finset.sum_congr rfl
      · intro i _
        simp only [coe_smul, Pi.smul_apply, TensorProduct.smul_tmul']
      · exact support_smul
      · intro i _
        simp only [zero_tmul, single_zero] }

end

section MvPolynomial

variable (σ : Type u) [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

noncomputable def MvPolynomial.tensorProductRight' :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) := {
  Finsupp.tensorProductLeft with
  map_smul' := fun s p => by
    induction p using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq =>
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply] at hp hq ⊢
      simp only [smul_add, LinearEquiv.map_add, hp, hq]
    | tmul p n =>
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply]
      rw [TensorProduct.smul_tmul']
      -- fails ! -- simp only [Finsupp.tensorProductLeft_apply_tmul]
      erw [Finsupp.tensorProductLeft_apply_tmul, Finsupp.tensorProductLeft_apply_tmul]
      rw [Finsupp.smul_sum, Finsupp.sum_smul_index]
      · simp only [Finsupp.smul_single]
        rfl
      · intro d
        simp only [zero_tmul, Finsupp.single_zero] }

noncomputable def MvPolynomial.tensorProductRight :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  LinearEquiv.ofLinear
    (TensorProduct.lift
      (Finsupp.lsum R (fun d => (ringLmapEquivSelf R R _).symm (Finsupp.lsingle d))))
    (Finsupp.lsum R
      (fun d ↦ (rTensor N (MvPolynomial.monomial d)).comp (TensorProduct.lid R N).symm.toLinearMap))
    (by ext i m n; simp [Finsupp.lsum])
    (by ext i m ; simp [Finsupp.lsum])

end MvPolynomial

section Polynomial

open Polynomial
variable {S : Type*} [CommSemiring S] [Algebra R S]

noncomputable def Polynomial.tensorProductRight :
    R[X] ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  LinearEquiv.ofLinear
    (TensorProduct.lift (Polynomial.lsum (fun i => (ringLmapEquivSelf R R _).symm (Finsupp.lsingle i))))
    (Finsupp.lsum R fun d ↦ (rTensor N (monomial d)).comp (TensorProduct.lid R N).symm.toLinearMap)
    (by ext i m n; simp [Polynomial.lsum])
    (by ext i m ; simp [Polynomial.lsum])

variable (S)
def Polynomial.toFinsuppLinearEquiv : S[X] ≃ₗ[S] (ℕ →₀ S) := {
  Polynomial.toFinsuppIso S  with
  map_smul' := fun r p => by simp }

variable {S}

noncomputable def LinearEquiv.rTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P :=
  LinearEquiv.ofLinear
    (LinearMap.rTensor P e.toLinearMap)
    (LinearMap.rTensor P e.symm.toLinearMap)
    (by simp [← LinearMap.rTensor_comp])
    (by simp [← LinearMap.rTensor_comp])

noncomputable def LinearEquiv.rTensor'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    M ⊗[R] P ≃ₗ[S] N ⊗[R] P := {
  (LinearEquiv.rTensor P (e.restrictScalars R)) with
  map_smul' := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, coe_coe, RingHom.id_apply] at hx hy ⊢
      simp only [smul_add, map_add, hx, hy]
    | tmul m p =>
      simp
      rw [TensorProduct.smul_tmul']
      simp [rTensor, TensorProduct.smul_tmul'] }

noncomputable def Polynomial.tensorProductRight' :
    Polynomial S ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  (LinearEquiv.rTensor' (R := R) (S := S) N (Polynomial.toFinsuppLinearEquiv S)).trans Finsupp.tensorProductLeft'

end Polynomial
