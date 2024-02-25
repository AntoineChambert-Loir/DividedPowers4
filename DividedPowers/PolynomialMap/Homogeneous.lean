/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.PolynomialMap.Coeff
import Mathlib.RingTheory.TensorProduct

section Homogeneous

universe u

namespace PolynomialMap

open scoped TensorProduct
open MvPolynomial

variable {R : Type u} {M N : Type*}
/- For the moment, need CommRing and AddCommGroup
  [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] -/
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A polynomial map is homogeneous if all its toFun are homogeneous -/
def IsHomogeneousOfDegree
    (p : ℕ) (f : PolynomialMap R M N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : S) (m : S ⊗[R] M),
    f.toFun S (r • m) = r ^ p • f.toFun S m
#align polynomial_map.is_homogeneous_of_degree PolynomialMap.IsHomogeneousOfDegree

lemma isHomogeneousOfDegree_iff (p : ℕ) (f : PolynomialMap R M N) :
    IsHomogeneousOfDegree p f ↔ ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : S) (m : S ⊗[R] M), f.toFun S (r • m) = r ^ p • f.toFun S m := by
  rfl

theorem IsHomogeneousOfDegree_add (p : ℕ) {f g : PolynomialMap R M N}
    (hf : f.IsHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree p) :
    (f + g).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsHomogeneousOfDegree_smul (p : ℕ) (r : R) {f : PolynomialMap R M N}
    (hf : f.IsHomogeneousOfDegree p) : (r • f).IsHomogeneousOfDegree p := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm r (s ^ p) (toFun f S m)

/-- The submodule of Homogeneous Polynomial maps -/
def grade (p : ℕ) : Submodule R (PolynomialMap R M N) where
  carrier   := IsHomogeneousOfDegree p
  add_mem' hf hg := IsHomogeneousOfDegree_add p hf hg
  smul_mem' r f hf := IsHomogeneousOfDegree_smul p r hf
  zero_mem' := by
    intro S _ _ r _
    simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_grade (f : PolynomialMap R M N) (p : ℕ) :
    f ∈ grade p ↔ IsHomogeneousOfDegree p f := by
  rfl

#check PolynomialMap.coeff

example (σ : Type*) (d : σ →₀ ℕ): MvPolynomial σ R →ₗ[R] R := by
  exact MvPolynomial.lcoeff d

example (f : MvPolynomial σ R →ₗ[R] R) : MvPolynomial σ R ⊗[R] N →ₗ[R] N :=
  (TensorProduct.lid R N).toLinearMap.comp (LinearMap.rTensor N f)

example (ι : Type*) : ι ↪ Option ι := by
  exact Function.Embedding.some

lemma isHomogeneousOfDegree_iff_coeff (f : PolynomialMap R M N) (p : ℕ) :
    IsHomogeneousOfDegree p f ↔
    ∀ {ι : Type u} [DecidableEq ι] [Fintype ι] (m : ι → M)
      (d : ι →₀ ℕ) (hd : d.sum (fun i n => n) ≠ p),
      PolynomialMap.coeff m f d = 0 := by
  constructor
  · intro hf ι _ _ m d hd
    let m' : Option ι → M
      | some i => m i
      | none => 0
    let θ : MvPolynomial ι R →ₐ[R] MvPolynomial (Option ι) R := by
      exact rename fun a => some a
    set μ : MvPolynomial ι R ⊗[R] M :=
      Finset.univ.sum (fun i => X i ⊗ₜ[R] m i)
    set μ' : MvPolynomial (Option ι) R ⊗[R] M :=
      Finset.univ.sum (fun i => X i ⊗ₜ[R] m' i)
    have : (LinearMap.rTensor M θ) μ = μ' := by simp
    rw [isHomogeneousOfDegree_iff] at hf
    specialize hf (MvPolynomial (Option ι) R)
    rw [coeff_eq]
    specialize hf (X none) μ'
    simp only [Finset.smul_sum, TensorProduct.smul_tmul'] at hf
    simp only [image_eq_coeff_sum] at hf
    simp only [Finsupp.smul_sum, TensorProduct.smul_tmul'] at hf
    let φ (e : Option ι →₀ ℕ) : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
      (TensorProduct.lid R N).toLinearMap.comp (LinearMap.rTensor N (MvPolynomial.lcoeff e))
    let hφ (e : Option ι →₀ ℕ) := LinearMap.congr_arg (f := φ e) hf
    simp only [map_finsupp_sum, LinearMap.map_smul] at hφ

    sorry
  · intro h
    intro S _ _ r m

    sorry
end PolynomialMap

end Homogeneous

section ConstantMap

namespace PolynomialMap

variable {R : Type u} [CommSemiring R]
  {M N : Type _} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

open TensorProduct LinearMap MvPolynomial

noncomputable def ofConstant (n : N) : PolynomialMap R M N where
  toFun S _ _ _:= TensorProduct.tmul R 1 n
  isCompat φ := by ext; simp
#align polynomial_map.of_constant PolynomialMap.ofConstant

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantHom : N →ₗ[R] (grade 0 : Submodule R (PolynomialMap R M N)) := {
  toFun := fun n ↦ {
    val := ofConstant n
    property := by
      simp only [grade, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
      intro S _ _ r sm
      simp only [pow_zero, one_smul]
      rfl }
  map_add'  := fun x y ↦ by
    simp only [AddSubmonoid.mk_add_mk, Subtype.mk.injEq, ofConstant]
    ext
    simp only [add_def_apply, TensorProduct.tmul_add]
  map_smul' := fun r x ↦ by
    simp only [RingHom.id_apply, SetLike.mk_smul_mk, Subtype.mk.injEq, ofConstant,
      TensorProduct.tmul_smul]
    rfl }

/-- Homogeneous Polynomial maps of degree 0 are constant maps -/
noncomputable def ofConstantEquiv :
    N ≃ₗ[R] (grade 0 : Submodule R (PolynomialMap R M N)) := {
  ofConstantHom with
  invFun    := fun f ↦ f.val.ground 0
  left_inv  := fun x ↦ by
    simp [ofConstantHom, ground, ofConstant]
  right_inv := fun x ↦ by
    obtain ⟨f, hf⟩ := x
    simp only [mem_grade, isHomogeneousOfDegree_iff] at hf
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [Subtype.ext_iff]
    rw [Subtype.coe_mk]
    simp [ofConstantHom, ground]
    ext S _ _ m
    conv_rhs =>
      rw [← one_smul (M := S) (f.toFun S m), ← pow_zero 0, ← hf S _ m]
      rw [zero_smul]
    have := f.isCompat_apply (algebraMap' R S) 0
    simp only [map_zero] at this
    simp [← this, ofConstant, isCompat_aux] }

end PolynomialMap

end ConstantMap

section Linear

namespace PolynomialMap

open LinearMap
open scoped TensorProduct

variable {R : Type u} [CommSemiring R]
  {M N : Type _} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

noncomputable def ofLinearMap (v : M →ₗ[R] N) : PolynomialMap R M N where
  toFun S _ _ := v.baseChange S
  isCompat φ := by
    ext
    simp only [← LinearMap.comp_apply, LinearMap.baseChange_eq_ltensor, Function.comp_apply, LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
#align polynomial_map.of_linear_map PolynomialMap.ofLinearMap

lemma ofLinearMap_mem_grade_one (v : M →ₗ[R] N) :
    ofLinearMap v ∈ grade 1 := by
  intro S _ _ r m
  simp [ofLinearMap]

theorem ofLinearMap_toFun (u : M →ₗ[R] N)
    (S : Type u) [CommSemiring S] [Algebra R S] :
  (ofLinearMap u).toFun S = LinearMap.baseChange S u := rfl
#align polynomial_map.of_linear_map_to_fun PolynomialMap.ofLinearMap_toFun

noncomputable def ofLinearMapHom :
    (M →ₗ[R] N) →ₗ[R] (grade 1 : Submodule R (PolynomialMap R M N)) where
  toFun := fun u ↦ ⟨ofLinearMap u, ofLinearMap_mem_grade_one u⟩
  map_add' u v := by
    ext S _ _ m
    simp only [ofLinearMap_toFun, LinearMap.baseChange_add, LinearMap.add_apply, AddSubmonoid.mk_add_mk, add_def_apply]
  map_smul' a v := by
    ext S _ _ m
    simp only [smul_def, ofLinearMap_toFun, LinearMap.baseChange_smul]
    rfl
#align polynomial_map.of_linear_map_hom PolynomialMap.ofLinearMapHom

theorem ofLinearMapHom_apply (v : M →ₗ[R] N) :
  ofLinearMapHom v = ofLinearMap v := rfl
#align polynomial_map.of_linear_map_hom_apply PolynomialMap.ofLinearMapHom_apply

open MvPolynomial

noncomputable example (m n : M) : (MvPolynomial (Fin 2) R) ⊗[R] M :=
  (X 0) ⊗ₜ[R] m + (X 1) ⊗ₜ[R] n

example : MvPolynomial (Fin 2) R →ₐ[R] R :=
  aeval (fun
    | 0 => 0
    | 1 => 1)

#check IsHomogeneousOfDegree

example (f : PolynomialMap R M N) (hf : f ∈ grade 1) (x : M) :
    f.toFun R ((1 : R) ⊗ₜ[R] x) = 1 ⊗ₜ[R] ground f x := by
  rw [mem_grade, isHomogeneousOfDegree_iff] at hf
  specialize hf R
  have hf' := isCompat_apply_ground f (R := R) (S := R)

  -- specialize hf (MvPolynomial (Fin 2) R) (X 0 + X 1) ((X 0) ⊗ₜ[R] m + (X 1) ⊗ₜ[R] n)
  sorry

def toLinearMap (f : (grade 1 : Submodule R (PolynomialMap R M N))) :
    M →ₗ[R] N := {
  toFun := ground (f : PolynomialMap R M N)
  map_add' := fun m n => by
    obtain ⟨f, hf⟩ := f; dsimp only
    rw [mem_grade, isHomogeneousOfDegree_iff] at hf
    specialize hf R
    have hf' := isCompat_apply_ground (R := R) (S := MvPolynomial (Fin 2) R) f

    sorry
  map_smul' := fun r x => by
    obtain ⟨f, hf⟩ := f; dsimp only [RingHom.id_apply]
    rw [mem_grade, isHomogeneousOfDegree_iff] at hf
    specialize hf R r ((1 : R) ⊗ₜ[R] x)
    simp only [TensorProduct.smul_tmul', TensorProduct.smul_tmul, pow_one] at hf
    apply (TensorProduct.lid R N).symm.injective
    simp only [TensorProduct.lid_symm_apply, map_smul]
    simp only [isCompat_apply_ground]
    exact hf }

def ofLinearMapEquiv :
    (M →ₗ[R] N) ≃ₗ[R] (grade 1 : Submodule R (PolynomialMap R M N)) := {
  ofLinearMapHom with
  invFun := sorry
  left_inv := sorry
  right_inv := sorry }


end Linear
