import DividedPowers.DPAlgebra.BaseChange
import DividedPowers.PolynomialMap.Homogeneous

/-

The universal homogeneous PolynomialMap from a module to the degree n
part of its DividedPowerAlgebra

Application : If M is free as a R-module with basis (e i),
  then the degree n component of DividedPowerAlgebra R M is free,
  with basis the family of all
  h.prod fun i n ↦ dp R n (e i)
  where h : ι →₀ ℕ satisfies h.total = n
-/
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

namespace DividedPowerAlgebra

open TensorProduct AlgEquiv LinearMap

/- TODO:  we need to prove that DividedPoweAlgebra.dpScalarExtensionEquiv
  is compatible with the graded structure and induces equivs componentwise -/
/-- The universal polynomial map (homogeneous of degree n) on a module -/
noncomputable
def gamma (n : ℕ) : PolynomialMap R M (DividedPowerAlgebra R M) where
  toFun' S _ _ := fun m ↦
    (DividedPowerAlgebra.dpScalarExtensionEquiv R S M).symm
      (DividedPowerAlgebra.dp S n m)
  isCompat' {S _ _ S' _ _} φ := by
    ext x
    apply rTensor_comp_dpScalarExtensionEquiv_symm_eq

theorem gamma_toFun (n : ℕ) {S : Type*} [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (gamma R M n).toFun S m = (dpScalarExtensionEquiv R S M).symm (dp S n m) := by
  obtain ⟨k, ψ, p, rfl⟩ := PolynomialMap.exists_lift m
  rw [← (gamma R M n).isCompat_apply, PolynomialMap.toFun_eq_toFun']
  simp only [gamma, rTensor_comp_dpScalarExtensionEquiv_symm_eq]

theorem isHomogeneousOfDegree_gamma (n : ℕ) :
    PolynomialMap.IsHomogeneousOfDegree n (DividedPowerAlgebra.gamma R M n) := by
  intro S _ _ r sm
  simp only [gamma]-- , dpScalarExtensionEquiv, ofAlgHom_symm_apply]
  apply (dpScalarExtensionEquiv R S M).injective
  simp only [apply_symm_apply, LinearMapClass.map_smul]
  rw [dp_smul]

theorem gamma_mem_grade (n : ℕ) (S : Type*) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (gamma R M n).toFun S m ∈ LinearMap.range (LinearMap.lTensor S (grade R M n).subtype) := by
  induction m using TensorProduct.induction_on generalizing n with
  | zero =>
    simp only [gamma_toFun, dp_null]
    split_ifs with h
    · rw [map_one, h]
      simp only [LinearMap.mem_range]
      use (1 : S) ⊗ₜ[R] ⟨(1 : DividedPowerAlgebra R M), one_mem R M⟩
      simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
      rw [Algebra.TensorProduct.one_def]
    · simp only [map_zero, zero_mem]
  | tmul s m =>
    simp only [gamma_toFun, dpScalarExtensionEquiv]
    simp only [ofAlgHom_symm_apply]
    rw [dpScalarExtensionInv_apply_dp]
    simp only [LinearMap.mem_range]
    use (s ^ n) ⊗ₜ[R] ⟨dp R n m, dp_mem_grade R M n m⟩
    simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype]
  | add x y hx hy =>
    simp only [gamma_toFun, dpScalarExtensionEquiv, ofAlgHom_symm_apply]
    simp only [dp_add, _root_.map_sum]
    apply Submodule.sum_mem
    rintro ⟨k, l⟩ hkl
    simp only [_root_.map_mul]
    specialize hx k
    specialize hy l
    simp only [gamma_toFun, dpScalarExtensionEquiv, ofAlgHom_symm_apply, LinearMap.mem_range] at hx hy
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    simp only [LinearMap.mem_range]
    -- we need the graded structure on the base change of a graded algebra
    rw [← hx', ← hy']
    sorry

/- to do this, it seems that we have to understand polynomial maps
valued into a submodule (in this case, it is a direct factor,
so it will exactly correspond to polynomial maps all of which evaluations
are valued into the submodule)
a “pure” submodule N (for which all base changes S ⊗[R] N → S⊗[R] M
are injective) would work as well -/

/-- The universal polynomial map (homogeneous of degree n) on a module,
  valued in the graded part of degree n -/
noncomputable
def gamma' (n : ℕ) : PolynomialMap R M (DividedPowerAlgebra.grade n (R := R) (M := M)) where
  toFun' S _ _ := sorry
  isCompat' {S _ _ S' _ _} φ := sorry

example {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ) :
  PolynomialMap.grade (R := R) (M := M) (N := N) n ≃ₗ[R]
    ((DividedPowerAlgebra.grade R M n) →ₗ[R] N) where
  toFun p := sorry
  map_add' := sorry
  map_smul' := sorry
  invFun f := sorry
  left_inv := sorry
  right_inv := sorry

/-- For `b : Basis ι R M`, a basis of `DividedPowerAlgebra.grade R M n` -/
noncomputable
def grade_basis (n : ℕ) {ι : Type*} (b : Basis ι R M) :
    Basis { h : ι →₀ ℕ // (h.sum fun i n ↦ n) = n } R (grade R M n) := by
  let v : (ι →₀ ℕ) → DividedPowerAlgebra R M :=
    fun h ↦ h.prod (fun i n ↦ dp R n (b i))
  have hv : ∀ h, v h ∈ grade R M (h.sum fun i n ↦ n) := sorry
  have v' : { h : ι →₀ ℕ // (h.sum fun i n ↦ n) = n} → grade R M n :=
    fun ⟨h, hh⟩ ↦ ⟨v h, by rw [← hh]; apply hv⟩
  apply Basis.mk (v := v')
  · /- Linear independence is the difficult part, it relies on the PolynomialMap
       interpretation -/
    sorry
  · /- It should be easy to prove that these elements generate
      * the `dp R n (b i)` generate -/
    sorry

theorem grade_free [Module.Free R M] (n : ℕ): Module.Free R (grade R M n) :=
  Module.Free.of_basis (grade_basis R M n (Module.Free.chooseBasis R M))

theorem toModule_free [Module.Free R M]  :
    Module.Free R (DividedPowerAlgebra R M) := by
  classical
  haveI : ∀ i, Module.Free R (grade R M i) := fun i ↦ grade_free R M i
  haveI : Module.Free R (DirectSum ℕ fun i ↦ ↥(grade R M i)) := by
    apply Module.Free.directSum
  apply Module.Free.of_equiv (DirectSum.decomposeLinearEquiv (grade R M)).symm
