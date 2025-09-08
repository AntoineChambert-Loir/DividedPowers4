/- Copyright ACL & MIdFF 2024 -/
import DividedPowers.PolynomialLaw.Basic2

universe u

/- # The polynomial law induced by a linear map

-/

open LinearMap TensorProduct

namespace LinearMap

open PolynomialLaw TensorProduct

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]


variable (r : R) (v w : M →ₗ[R] N)

/-- The `R`-linear map sending a linear map `v : M →ₗ[R] N` to the polynomial law given by
base change of `v`. -/
noncomputable def toPolynomialLaw : (M →ₗ[R] N) →ₗ[R] M →ₚₗ[R] N where
  toFun v :=
  { toFun' S _ _ := v.baseChange S
    isCompat' φ  := by
      ext
      simp [← LinearMap.comp_apply, baseChange_eq_ltensor, Function.comp_apply] }
  map_add' v w := by ext S _ _ m; simp
  map_smul' r w := by ext S _ _ m; simp

theorem toPolynomialLaw_ground_apply (m : M) : v.toPolynomialLaw m = v m := by
  simp only [ground_apply]
  exact (LinearEquiv.eq_symm_apply (TensorProduct.lid R N)).mp rfl

theorem toPolynomialLaw_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    v.toPolynomialLaw.toFun' S = LinearMap.baseChange S v := rfl

theorem toPolynomialLaw_toFun (S : Type*) [CommSemiring S] [Algebra R S] :
    v.toPolynomialLaw.toFun S = v.baseChange S := by
  ext sm
  obtain ⟨n, φ, p, rfl⟩ := exists_lift sm
  simp only [← isCompat_apply, toFun_eq_toFun', toPolynomialLaw_toFun', baseChange_eq_ltensor,
    ← LinearMap.comp_apply, rTensor_comp_lTensor, lTensor_comp_rTensor]

theorem toPolynomialLaw_id :
    (LinearMap.id).toPolynomialLaw = PolynomialLaw.id (R := R) (M := M) := by
  ext S _ _ m
  simp [toPolynomialLaw_toFun', id_apply']

theorem toPolynomialLaw_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (g.comp f).toPolynomialLaw = g.toPolynomialLaw.comp f.toPolynomialLaw := by
  ext S _ _ m
  simp [toPolynomialLaw_toFun', baseChange_comp, comp_toFun']

end LinearMap

#lint
