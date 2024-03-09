import Mathlib.RingTheory.TensorProduct
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Coeff

open TensorProduct LinearMap

open scoped TensorProduct



universe u v w

noncomputable section

open DirectSum TensorProduct

open Set LinearMap Submodule

section MvPolynomial

namespace MvPolynomial

variable {R : Type*} [CommSemiring R]
def lcoeff (k : ι →₀ ℕ) : MvPolynomial ι R →ₗ[R] R where
  toFun     := coeff k
  map_add'  := coeff_add k
  map_smul' := coeff_smul k

theorem lcoeff_apply (k : ι →₀ ℕ) (f : MvPolynomial ι R) :
    lcoeff k f = coeff k f := rfl

end MvPolynomial

end MvPolynomial

section TensorProduct

namespace TensorProduct

variable {ι : Type*} [DecidableEq ι]
variable {R : Type u} {M : Type v} {N : Type w}
[CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The tensor product of `i →₀ M` and `N` is linearly equivalent to `i →₀ M ⊗[R] N` -/
noncomputable def finsuppLeft :
    (ι →₀ M) ⊗[R] N ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  (congr (finsuppLEquivDirectSum R M ι) (LinearEquiv.refl R N)).trans
    ((directSumLeft R (fun _ : ι => M) N).trans
      (finsuppLEquivDirectSum R (M ⊗[R] N) ι).symm)

lemma finsuppLeft_apply_tmul (p : ι →₀ M) (n : N) :
    finsuppLeft (p ⊗ₜ[R] n) = p.sum (fun i m ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp only [finsuppLeft, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply]
  conv_lhs => rw [← Finsupp.sum_single p]
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_finsupp_sum]
  simp only [finsuppLEquivDirectSum_single]
  rw [← LinearEquiv.eq_symm_apply]
  simp only [map_finsupp_sum]
  simp only [directSumLeft_symm_lof_tmul]
  simp only [Finsupp.sum, sum_tmul]

lemma finsuppLeft_apply_tmul_apply (p : ι →₀ M) (n : N) (i : ι) :
    finsuppLeft (p ⊗ₜ[R] n) i = p i ⊗ₜ[R] n := by
  rw [finsuppLeft_apply_tmul]
  simp only [Finsupp.sum_apply]
  conv_rhs => rw [← Finsupp.single_eq_same (a := i) (b := p i ⊗ₜ[R] n)]
  apply Finsupp.sum_eq_single i
  · exact fun _ _ ↦ Finsupp.single_eq_of_ne
  · intro _
    simp

lemma finsuppLeft_symm_apply_single (i : ι) (m : M) (n : N) :
    finsuppLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [finsuppLeft, Finsupp.lsum]

/-- The tensor product of `M` and `i →₀ N` is linearly equivalent to `i →₀ M ⊗[R] N` -/
noncomputable def finsuppRight :
    M ⊗[R] (ι →₀ N) ≃ₗ[R] ι →₀ (M ⊗[R] N) :=
  (congr (LinearEquiv.refl R M) (finsuppLEquivDirectSum R N ι)).trans
    ((directSumRight R M (fun _ : ι => N)).trans
      (finsuppLEquivDirectSum R (M ⊗[R] N) ι).symm)

lemma finsuppRight_apply_tmul (m : M) (p : ι →₀ N) :
    finsuppRight (m ⊗ₜ[R] p) = p.sum (fun i n ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp [finsuppRight]
  conv_lhs => rw [← Finsupp.sum_single p]
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_finsupp_sum]
  simp only [finsuppLEquivDirectSum_single]
  rw [← LinearEquiv.eq_symm_apply]
  simp only [map_finsupp_sum]
  simp only [directSumRight_symm_lof_tmul]
  simp only [Finsupp.sum, tmul_sum]

lemma finsuppRight_symm_apply_single (i : ι) (m : M) (n : N) :
    finsuppLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [finsuppLeft, Finsupp.lsum]

variable {S : Type*} [CommSemiring S] [Algebra R S]
  [Module S M] [IsScalarTower R S M]

lemma finsuppLeft_smul' (s : S) (t : (ι →₀ M) ⊗[R] N) :
    finsuppLeft (s • t) = s • finsuppLeft t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, LinearEquiv.coe_coe, RingHom.id_apply] at hx hy ⊢
    simp only [smul_add, map_add, hx, hy]
  | tmul p n =>
    simp only [smul_tmul', finsuppLeft_apply_tmul]
    rw [Finsupp.smul_sum]
    simp only [Finsupp.smul_single]
    apply Finsupp.sum_smul_index'
    simp

/-- When `M` is also an `S`-module, then `TensorProduct.finsuppLeft R M N``
  is an `S`-linear equiv -/
noncomputable def finsuppLeft' :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ (M ⊗[R] N) := {
  finsuppLeft with
  map_smul' := finsuppLeft_smul' }

/- -- TODO : reprove using the existing heterobasic lemmas
noncomputable example :
    (ι →₀ M) ⊗[R] N ≃ₗ[S] ι →₀ (M ⊗[R] N) := by
  have f : (⨁ (i₁ : ι), M) ⊗[R] N ≃ₗ[S] ⨁ (i : ι), M ⊗[R] N := sorry
  exact (AlgebraTensorModule.congr
    (finsuppLEquivDirectSum S M ι) (LinearEquiv.refl R N)).trans
    (f.trans (finsuppLEquivDirectSum S (M ⊗[R] N) ι).symm) -/

end TensorProduct

end TensorProduct

end

section Polynomial


open TensorProduct LinearMap

variable {R : Type u} {M : Type v} {N : Type w}
[CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

-- keep ?
noncomputable def LinearEquiv.rTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)

theorem LinearEquiv.rTensor_toLinearMap
  (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
  (e.rTensor P).toLinearMap = e.toLinearMap.rTensor P := rfl

theorem LinearEquiv.rTensor_symm
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    LinearEquiv.rTensor P e.symm = (LinearEquiv.rTensor P e).symm := by
  rfl

-- TODO : lTensor ?

variable {S : Type*} [CommSemiring S] [Algebra R S]

lemma TensorProduct.map_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M →ₗ[S] N) (f : P →ₗ[R] Q) :
    IsLinearMap S (TensorProduct.map (e.restrictScalars R) f) where
  map_add := LinearMap.map_add _
  map_smul := fun s t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [smul_add, map_add] at hx hy ⊢
      simp only [hx, hy]
    | tmul m p =>
      rw [smul_tmul']
      simp only [map_tmul, coe_restrictScalars, map_smul]
      rfl

lemma TensorProduct.congr_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P]
    {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (e : M ≃ₗ[S] N) (f : P ≃ₗ[R] Q) :
    IsLinearMap S (TensorProduct.congr (e.restrictScalars R) f) :=
  TensorProduct.map_isLinearMap' e.toLinearMap f.toLinearMap

lemma LinearEquiv.rTensor_isLinearMap'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    IsLinearMap S (LinearEquiv.rTensor P (e.restrictScalars R)) :=
  TensorProduct.map_isLinearMap' e.toLinearMap _

noncomputable def LinearEquiv.rTensor'
    [Module S M] [IsScalarTower R S M] [Module S N] [IsScalarTower R S N]
    (P : Type*) [AddCommMonoid P] [Module R P] (e : M ≃ₗ[S] N) :
    M ⊗[R] P ≃ₗ[S] N ⊗[R] P := {
  (LinearEquiv.rTensor P (e.restrictScalars R)) with
  map_smul' := (LinearEquiv.rTensor_isLinearMap' P e).map_smul }

section Polynomial

namespace Polynomial


def toFinsuppLinearEquiv : S[X] ≃ₗ[S] (ℕ →₀ S) := {
  toFinsuppIso S  with
  map_smul' := fun r p => by simp }

noncomputable def rTensorEquiv :
    Polynomial R ⊗[R] N ≃ₗ[R] ℕ →₀ N :=
  (LinearEquiv.rTensor N toFinsuppLinearEquiv).trans
    (TensorProduct.finsuppLeft.trans
      (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N)))

noncomputable def rTensor' :
    Polynomial S ⊗[R] N ≃ₗ[S] ℕ →₀ (S ⊗[R] N) :=
  (LinearEquiv.rTensor' N toFinsuppLinearEquiv).trans TensorProduct.finsuppLeft'

end Polynomial

end Polynomial

section MvPolynomial

namespace MvPolynomial

variable (σ : Type u) [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

noncomputable def rTensor :
    MvPolynomial σ S ⊗[R] N ≃ₗ[S] (σ →₀ ℕ) →₀ (S ⊗[R] N) := {
  finsuppLeft' with
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
      ext d
      erw [finsuppLeft_apply_tmul_apply]
      simp only [Finsupp.smul_apply]
      erw [finsuppLeft_apply_tmul_apply]
      rw [smul_tmul', Finsupp.smul_apply] }

lemma rTensor_apply_tmul_apply
    (p : MvPolynomial σ S) (n : N) (k) :
    (MvPolynomial.rTensor σ) (p ⊗ₜ[R] n) k = MvPolynomial.coeff k p ⊗ₜ[R] n := by
  dsimp only [rTensor, LinearEquiv.trans_apply]
  simp
  erw [TensorProduct.finsuppLeft_apply_tmul_apply]
  rfl

noncomputable def scalarRTensor :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
    LinearEquiv.trans (rTensor σ) (Finsupp.mapRange.linearEquiv (TensorProduct.lid R N))
/-  LinearEquiv.ofLinear
    (TensorProduct.lift
      (Finsupp.lsum R (fun d => (ringLmapEquivSelf R R _).symm (Finsupp.lsingle d))))
    (Finsupp.lsum R
      (fun d ↦ TensorProduct.mk R (MvPolynomial σ R) N ((monomial d) 1))) -- (rTensor (MvPolynomial.monomial d)).comp (TensorProduct.lid R N).symm.toLinearMap))
    (by ext i m n; simp [Finsupp.lsum])
    (by ext i m ; simp [Finsupp.lsum]) -/

lemma scalarRTensor_apply_tmul_apply
    (p : MvPolynomial σ R) (n : N) (k) :
    (scalarRTensor σ) (p ⊗ₜ[R] n) k = MvPolynomial.coeff k p • n := by
  dsimp only [scalarRTensor, LinearEquiv.trans_apply]
  simp
  erw [TensorProduct.finsuppLeft_apply_tmul_apply]
  rfl

theorem scalarRTensor_apply (pn : MvPolynomial σ R ⊗[R] N) (d : σ →₀ ℕ) :
  (scalarRTensor σ) pn d = (TensorProduct.lid R N)
    ((LinearMap.rTensor N (MvPolynomial.lcoeff d)) pn) := by
  induction pn using TensorProduct.induction_on with
  | zero => simp
  | tmul p n =>
      simp only [rTensor_tmul, TensorProduct.lid_tmul]
      simp only [scalarRTensor_apply_tmul_apply]
      rfl
  | add p q h h' => simp [h, h']

lemma scalarRTensor_symm_apply_single (k : σ →₀ ℕ) (n : N) :
  (scalarRTensor σ).symm (Finsupp.single k n) = (monomial k) 1 ⊗ₜ[R] n := by
  rw [LinearEquiv.symm_apply_eq]
  dsimp only [scalarRTensor, LinearEquiv.trans_apply]
  apply Finsupp.ext
  intro l
  simp only [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange.linearMap_apply,
    LinearEquiv.coe_coe, Finsupp.mapRange_apply]
  rw [rTensor_apply_tmul_apply, ← LinearEquiv.symm_apply_eq]
  simp only [lid_symm_apply, coeff_monomial, Finsupp.single_apply]
  split_ifs; rfl; simp

lemma scalarRTensor_symm_apply (p : (σ →₀ ℕ) →₀ N) :
    (scalarRTensor σ).symm p = p.sum (fun k n => (monomial k) 1 ⊗ₜ[R] n) := by
  rw [LinearEquiv.symm_apply_eq]
  dsimp only [scalarRTensor, LinearEquiv.trans_apply]
  apply Finsupp.ext
  intro l
  simp only [Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange.linearMap_apply,
    LinearEquiv.coe_coe, Finsupp.mapRange_apply]
  simp only [map_finsupp_sum]
  rw [Finsupp.sum_apply]
  simp only [rTensor_apply_tmul_apply]
  rw [← LinearEquiv.symm_apply_eq]
  rw [Finsupp.sum_eq_single l]
  · simp only [lid_symm_apply, coeff_monomial, ↓reduceIte]
  · exact fun d _ hd' ↦ by simp only [coeff_monomial, if_neg hd', zero_tmul]
  · exact fun _ ↦ by simp only [tmul_zero]

end MvPolynomial

end MvPolynomial

#exit

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

lemma Finsupp.tensorProductRight_apply_tmul (m : M) (p : ι →₀ N) :
  Finsupp.tensorProductRight (m ⊗ₜ[R] p) =
    p.sum (fun i n ↦ Finsupp.single i (m ⊗ₜ[R] n)) := by
  simp only [tensorProductRight]
  simp only [LinearEquiv.trans_apply]
  simp only [comm_tmul, tensorProductLeft_apply_tmul]
  simp only [mapRange.linearEquiv_apply, mapRange.linearMap_apply, LinearEquiv.coe_coe]
  ext i
  simp only [mapRange_apply, sum_apply, map_finsupp_sum]
  apply Finsupp.sum_congr
  intro x _
  simp only [single_apply]
  split_ifs with hxi
  · simp only [comm_tmul]
  · simp only [_root_.map_zero]

lemma Finsupp.tensorProductRight_symm_apply_single (i : ι) (m : M) (n : N) :
    Finsupp.tensorProductLeft.symm (Finsupp.single i (m ⊗ₜ[R] n)) =
      Finsupp.single i m ⊗ₜ[R] n := by
  simp [Finsupp.tensorProductLeft, Finsupp.lsum]

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

noncomputable def LinearEquiv.rTensor₁
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P :=
  LinearEquiv.ofLinear
    (LinearMap.rTensor P e.toLinearMap)
    (LinearMap.rTensor P e.symm.toLinearMap)
    (by simp [← LinearMap.rTensor_comp])
    (by simp [← LinearMap.rTensor_comp])

noncomputable def LinearEquiv.rTensor
    (P : Type*) (e : M ≃ₗ[R] N)  [AddCommMonoid P] [Module R P] :
    M ⊗[R] P ≃ₗ[R] N ⊗[R] P := TensorProduct.congr e (refl R P)

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
