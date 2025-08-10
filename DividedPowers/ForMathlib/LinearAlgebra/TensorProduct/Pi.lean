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

-- **MI** : I am not sure about whether we want these `coe` lemmas to be `simp`.

--@[simp]
lemma coe_piRightHom : ⇑(piRightHom R S N M) = (piRightHom R R N M) := rfl

--@[simp]
lemma coe_piRight [Fintype ι] [DecidableEq ι] : ⇑(piRight R S N M) = (piRight R R N M) := rfl

--@[simp]
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
  simp [piRightHom_rTensor_eq_rTensor_piRightHom, coe_piRightHom]

variable {R S N} [Fintype ι] [DecidableEq ι]

@[simp]
lemma piRight_symm_zero :
    ((piRight R S N M).symm fun _ ↦ 0) = 0 := by
  rw [← Pi.zero_def, map_zero]

lemma smul_tmul_proj_eq (r' : ι → S) (i : ι) (s : S) (m : Π i, M i) :
    r' i • s ⊗ₜ[R] m i = (piRight R S S M)
      (r' i • s ⊗ₜ[R] Pi.single i (m i)) i := by simp

theorem smul_piRight_apply (sm : S ⊗[R] (Π i, M i)) (r' : ι → S) (i : ι) :
    r' i • (piRight R S S M) sm i =
      (piRight R S S M) ((piRight R S S M).symm fun i ↦ r' i • (piRight R S S M) sm i) i := by
  rw [← Pi.smul_apply, ← map_smul]
  induction sm using TensorProduct.induction_on with
  | zero =>
    simp [-piRight_apply, smul_zero, map_zero, piRight_symm_zero]
  | add x y hx hy =>
    simp [-piRight_apply, smul_add, ← Pi.add_def, map_add, Pi.add_apply]
  | tmul s m =>
    simp only [map_smul, piRight_apply, piRightHom_tmul, Pi.smul_apply, coe_piRight_symm,
      coe_piRightHom]
    rw [← piRight_apply, smul_tmul_proj_eq]
    simp

theorem smul_const_piRight_apply (sm : S ⊗[R] (Π i, M i)) (r : S) :
    r • (piRight R S S M) sm = (piRight R S S M) (r • sm) := by
  rw [← Pi.smul_apply]
  induction sm using TensorProduct.induction_on with
  | zero =>
    simp only [coe_piRight, Pi.smul_apply, map_zero, smul_zero]
  | add x y hx hy =>
    simp only [coe_piRight, Pi.smul_apply, map_add, piRight_apply, coe_piRightHom, smul_add,
      map_smul]
  | tmul s m =>
    simp only [coe_piRight, Pi.smul_apply, piRight_apply, piRightHom_tmul, map_smul]

variable (R S N M) in
def projRight (i : ι) : N ⊗[R] (Π i, M i) →ₗ[S] N ⊗[R] M i :=
  (LinearMap.proj i).comp (piRight R S N M).toLinearMap

lemma piRight_eq_pi_projRight :
    (piRight R S N M).toLinearMap = LinearMap.pi (projRight R S N M) := by
  ext n i mi j
  simp [projRight]

lemma piRight_symm_comp_pi_prodRight :
    (piRight R S N M).symm.toLinearMap.comp (LinearMap.pi (projRight R S N M)) = LinearMap.id := by
  rw [← piRight_eq_pi_projRight, LinearEquiv.symm_comp]

lemma piRight_symm_comp_pi_prodRight_apply (x : N ⊗[R] (Π i, M i)) :
    (piRight R S N M).symm (LinearMap.pi (projRight R S N M) x) = x := by
  erw [← LinearMap.comp_apply, piRight_symm_comp_pi_prodRight, LinearMap.id_apply]

lemma projRight_piRight_apply (i : ι) (f : Π i, N ⊗[R]  M i)  :
    (projRight R S N M i) ((piRight R S N M).symm f) = f i := by
  simp [projRight]

lemma projRight_piRight (i : ι) :
    (projRight R S N M i).comp (piRight R S N M).symm.toLinearMap = LinearMap.proj i :=
  LinearMap.ext_iff.mpr fun x ↦ projRight_piRight_apply i x

variable (R S N M) in
def singleRight (i : ι) : N ⊗[R] M i →ₗ[S] N ⊗[R] (Π i, M i) :=
  (piRight R S N M).symm.toLinearMap.comp (LinearMap.single S (fun i ↦ (N ⊗[R] M i)) i)

lemma singleRight_tmul (i : ι) (n : N) (m : M i) :
    singleRight R S N M i (n ⊗ₜ m) = n ⊗ₜ Pi.single i m := by
  simp [singleRight]

lemma projRight_singleRight_eq_same (i : ι) (nm : N ⊗[R] M i) :
    (projRight R S N M i) (singleRight R S N M i nm) = nm := by
  simp [projRight, singleRight]

lemma projRight_singleRight (i : ι):
    (projRight R S N M i).comp (singleRight R S N M i) = LinearMap.id :=
  LinearMap.ext_iff.mpr fun x ↦ projRight_singleRight_eq_same i x

variable (S) in
lemma right_ext_iff {x y : N ⊗[R] (Π i, M i)} :
    x = y ↔ ∀ i, projRight R S N M i x = projRight R S N M i y := by
  simp [← (piRight R R N M).injective.eq_iff, projRight]
  exact funext_iff

variable (R S N M) in
def compRight (i : ι) : N ⊗[R] (Π i, M i) →ₗ[S] N ⊗[R] (Π i, M i) :=
  (singleRight R S N M i).comp (projRight R S N M i)

lemma sum_compRight (nm : N ⊗[R] (Π i, M i)) : ∑ i, (compRight R S N M i nm) = nm :=
  (right_ext_iff S).mpr fun i ↦ by simp [projRight, compRight, singleRight]

lemma compRight_tmul (i : ι) (n : N) (m : Π i, M i) :
    (compRight R S N M i (n ⊗ₜ (fun i ↦ m i))) = singleRight R S N M i (n ⊗ₜ m i) := by
  simp [compRight, singleRight, projRight]

lemma compRight_piRight_tmul (i : ι) (n : ι → N) (m : Π i, M i) :
    (compRight R S N M i ((piRight R S N M).symm fun i ↦ n i ⊗ₜ m i)) =
      singleRight R S N M i (n i ⊗ₜ m i) := by
  simp [compRight, singleRight, projRight]

lemma compRight_singleRight_eq_same (i : ι) (nm : N ⊗[R] M i):
    (compRight R S N M i) (singleRight R S N M i nm) = (singleRight R S N M i nm) := by
  simp [compRight, singleRight, projRight]

lemma compRight_singleRight (i j : ι) (nm : N ⊗[R] M j):
    (compRight R S N M i) (singleRight R S N M j nm) =
      if i = j then (singleRight R S N M j nm) else 0 := by
  split_ifs with h
  · rw [h]
    exact compRight_singleRight_eq_same j nm
  · simp [compRight, singleRight, projRight, Pi.single_eq_of_ne h]

lemma projRight_compRight_eq_same (i : ι) (nm : N ⊗[R] (Π i, M i)) :
    projRight R S N M i (compRight R S N M i nm) = projRight R S N M i nm := by
  simp [compRight, singleRight, projRight]

lemma projRight_compRight (i j : ι) (nm : N ⊗[R] (Π i, M i)) :
    projRight R S N M i (compRight R S N M j nm) =
      if i = j then projRight R S N M i nm  else 0 := by
  split_ifs with h
  · exact h ▸ projRight_compRight_eq_same i nm
  · simp [compRight, singleRight, projRight, Pi.single_eq_of_ne h]

lemma projRight_compRight_piRight_tmul (i : ι) (n : ι → N) (m : Π i, M i) :
    projRight R S N M i (compRight R S N M i ((piRight R S N M).symm fun i ↦ n i ⊗ₜ m i)) =
      (n i ⊗ₜ m i) := by
  simp [compRight, singleRight, projRight]


end TensorProduct
