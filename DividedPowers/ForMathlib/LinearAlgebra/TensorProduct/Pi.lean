/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!

# Tensor product and products

In this file we expand the API to work with the tensor product with arbitrary and finite products.

## Main definitions
- `TensorProduct.projRight`: the `S`-linear map sending `x : N ⊗[R] (Π i, M i)` to its `i`th
  component in `N ⊗[R] M i`.
- `TensorProduct.singleRight`: the `S`-linear map sending `x : N ⊗[R] M i` to the term of
  `N ⊗[R] (Π i, M i)` whose `i`th component is given by `x`, and whose remaining components
  are zero.
- `TensorProduct.compRight`: the `S`-linear map sending `x : N ⊗[R] (Π i, M i)` to the term of
  `N ⊗[R] (Π i, M i)` whose `i`th component agrees with that of `x`, and whose remaining
  components are zero.

## TODO
- Remove `TensorProduct.piRight_apply` from the Mathlib simp set.
- Rename `TensorProduct.piRight` to `TensorProduct.piRightEquiv` in Mathlib, for consistency
  with with `TensorProduct.piRightHom`.
-/

noncomputable section

namespace TensorProduct

variable {ι R S T N P : Type*} {M : ι → Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring T] [Algebra R T] [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]

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

lemma coe_piRightHom : (piRightHom R S S M) = ⇑(piRightHom R R S M) := rfl

lemma coe_piRight [Fintype ι] [DecidableEq ι] : ⇑(piRight R S N M) = (piRight R R N M) := rfl

lemma coe_piRight_symm [Fintype ι] [DecidableEq ι] :
    ⇑(piRight R S N M).symm = (piRight R R N M).symm := by
  ext d
  simp only [LinearEquiv.symm_apply_eq, coe_piRight, LinearEquiv.apply_symm_apply]

lemma piRightHom_smul_proj (s : S) (m : S ⊗[R] (Π i, M i)) :
    (piRightHom R R S M) (s • m) = s • (piRightHom R R S M) m := by
  rw [← coe_piRightHom, map_smul, coe_piRightHom]

variable [Fintype ι] [DecidableEq ι]

lemma piRight_smul_proj (s : S) (m : S ⊗[R] (Π i, M i)) :
    (piRight R R S M) (s • m) = s • (piRight R R S M) m  := by
  simp [piRight_apply, piRightHom_smul_proj]

lemma piRight_rTensor_eq_rTensor_piRight' (ψ : T →ₐ[R] S) (m : T ⊗[R] ((i : ι) → M i)) (i : ι) :
    (piRight R S S M) ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap) m) i =
      LinearMap.rTensor (M i) ψ.toLinearMap (piRight R T T M m i) := by
  simp [piRightHom_rTensor_eq_rTensor_piRightHom, coe_piRightHom]

@[simp]
lemma piRight_symm_zero : ((piRight R S N M).symm fun _ ↦ 0) = 0 := by
  rw [← Pi.zero_def, map_zero]

lemma smul_tmul_proj_eq (r' : ι → S) (i : ι) (s : S) (m : Π i, M i) :
    r' i • s ⊗ₜ[R] m i = (piRight R S S M) (r' i • s ⊗ₜ[R] Pi.single i (m i)) i := by simp

variable (sm : S ⊗[R] (Π i, M i)) (s : S) (s' : ι → S) (i : ι)

theorem smul_piRight_apply : s' i • (piRight R S S M) sm i =
    (piRight R S S M) ((piRight R S S M).symm (s' • (piRight R S S M sm))) i := by
  rw [← LinearEquiv.trans_apply]
  simp

theorem smul_const_piRight_apply : s • (piRight R S S M) sm = (piRight R S S M) (s • sm) := by
  rw [← Pi.smul_apply]
  simp

variable (R S N M) in
/-- The `S`-linear map sending `x : N ⊗[R] (Π i, M i)` to its `i`th component in `N ⊗[R] M i`. -/
@[irreducible]
def projRight : N ⊗[R] (Π i, M i) →ₗ[S] N ⊗[R] M i :=
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
/-- The `S`-linear map sending `x : N ⊗[R] M i` to the term of `N ⊗[R] (Π i, M i)` whose `i`th
component is given by `x`, and whose remaining components are zero. -/
@[irreducible]
def singleRight (i : ι) : N ⊗[R] M i →ₗ[S] N ⊗[R] (Π i, M i) :=
  (piRight R S N M).symm.toLinearMap.comp (LinearMap.single S (fun i ↦ (N ⊗[R] M i)) i)

@[simp]
lemma singleRight_tmul (i : ι) (n : N) (m : M i) :
    singleRight R S N M i (n ⊗ₜ m) = n ⊗ₜ Pi.single i m := by
  simp [singleRight]

lemma projRight_singleRight_eq_same (i : ι) (nm : N ⊗[R] M i) :
    (projRight R S N M i) (singleRight R S N M i nm) = nm := by
  simp [projRight, singleRight]

lemma projRight_singleRight_eq_zero_of_ne {i j : ι} (hij : i ≠ j) (nm : N ⊗[R] M j) :
    (projRight R S N M i) (singleRight R S N M j nm) = 0 := by
  simp [projRight, singleRight, Pi.single_eq_of_ne hij]

lemma projRight_singleRight (i : ι):
    (projRight R S N M i).comp (singleRight R S N M i) = LinearMap.id :=
  LinearMap.ext_iff.mpr fun x ↦ projRight_singleRight_eq_same i x

variable (S) in
lemma right_ext_iff {x y : N ⊗[R] (Π i, M i)} :
    x = y ↔ ∀ i, projRight R S N M i x = projRight R S N M i y := by
  simp [← (piRight R R N M).injective.eq_iff, projRight]
  exact funext_iff

variable (S) in
@[ext]
lemma right_ext {x y : N ⊗[R] (Π i, M i)}
    (h : ∀ i, projRight R S N M i x = projRight R S N M i y ) : x = y :=
  (right_ext_iff S).mpr h

variable (R S N M) in
/-- The `S`-linear map sending `x : N ⊗[R] (Π i, M i)` to the term of `N ⊗[R] (Π i, M i)` whose
`i`th component agrees with that of `x`, and whose remaining components are zero. -/
@[irreducible]
def compRight (i : ι) : N ⊗[R] (Π i, M i) →ₗ[S] N ⊗[R] (Π i, M i) :=
  (singleRight R S N M i).comp (projRight R S N M i)

lemma sum_compRight (nm : N ⊗[R] (Π i, M i)) : ∑ i, (compRight R S N M i nm) = nm :=
  (right_ext_iff S).mpr fun i ↦ by simp [projRight, compRight, singleRight]

@[simp]
lemma compRight_tmul (i : ι) (n : N) (m : Π i, M i) :
    (compRight R S N M i (n ⊗ₜ (fun i ↦ m i))) = singleRight R S N M i (n ⊗ₜ m i) := by
  simp [compRight, singleRight, projRight]

@[simp]
lemma compRight_piRight_tmul (i : ι) (n : ι → N) (m : Π i, M i) :
    (compRight R S N M i ((piRight R S N M).symm fun i ↦ n i ⊗ₜ m i)) =
      singleRight R S N M i (n i ⊗ₜ m i) := by
  simp [compRight, singleRight, projRight]

lemma compRight_singleRight_eq_same (i : ι) (nm : N ⊗[R] M i) :
    (compRight R S N M i) (singleRight R S N M i nm) = (singleRight R S N M i nm) := by
  simp [compRight, singleRight, projRight]

lemma compRight_singleRight_eq_zero_of_ne {i j : ι} (hij : i ≠ j) (nm : N ⊗[R] M j) :
    (compRight R S N M i) (singleRight R S N M j nm) = 0 := by
  simp [compRight, singleRight, projRight, Pi.single_eq_of_ne hij]

lemma compRight_singleRight (i j : ι) (nm : N ⊗[R] M j) :
    (compRight R S N M i) (singleRight R S N M j nm) =
      if i = j then (singleRight R S N M j nm) else 0 := by
  split_ifs with h
  · rw [h]
    exact compRight_singleRight_eq_same j nm
  · exact compRight_singleRight_eq_zero_of_ne h nm

lemma projRight_compRight_eq_same (i : ι) (nm : N ⊗[R] (Π i, M i)) :
    projRight R S N M i (compRight R S N M i nm) = projRight R S N M i nm := by
  simp [compRight, singleRight, projRight]

lemma projRight_compRight_eq_zero_of_ne {i j : ι} (hij : i ≠ j) (nm : N ⊗[R] (Π i, M i)) :
    projRight R S N M i (compRight R S N M j nm) = 0 := by
  simp [compRight, singleRight, projRight, Pi.single_eq_of_ne hij]

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
