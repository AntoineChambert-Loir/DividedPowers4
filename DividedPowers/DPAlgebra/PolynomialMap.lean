import DividedPowers.PolynomialMap.Homogeneous
import DividedPowers.DPAlgebra.Graded.Basic
import DividedPowers.DPAlgebra.BaseChange

/-

The universal homogeneous PolynomialMap from a module to the degree n
part of its DividedPowerAlgebra

-/
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/- -- To turn an algebra into an add group if the
coefficient semiring is a ring
-- would pose problems
instance (R : Type u) [CommRing R]
    (S : Type _) [CommRing S] [Algebra R S]
    (M : Type _) [AddCommMonoid M] [Module R M] : AddCommGroup (S ⊗[R] M) := {
  neg := fun m ↦ (-1 : R) • m
  add_left_neg := fun a ↦ by
    dsimp
    nth_rewrite 2 [← one_smul R a]
    rw [← add_smul, add_left_neg, zero_smul]
  add_comm := fun a b ↦ add_comm a b }

-/

namespace DividedPowerAlgebra

open TensorProduct AlgEquiv LinearMap

example {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B)
  {ι : Type*} (s : Finset ι) (f : ι → A) :
  e (s.sum f) = s.sum (e ∘ f) := by
  rw [_root_.map_sum]
  simp only [Function.comp_apply]

noncomputable example {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
  A ⊗[R] S →ₐ[R] B ⊗[R] S :=
  Algebra.TensorProduct.map f (AlgHom.id R S)

example {R S T A B : Type*} [CommRing R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  (f : A →ₐ[R] B) (g : S →ₐ[R] T) (x : A ⊗[R] S):
  Algebra.TensorProduct.map f g x =
    TensorProduct.map f g x := by
  rfl

instance (R S S' M M': Type*) [CommSemiring R] [AddCommMonoid S] [AddCommMonoid S']
  [AddCommMonoid M] [AddCommMonoid M'] [Module R S] [Module R S'] [Module R M] [Module R M']: AddMonoidHomClass (S ⊗[R] M →ₗ[R] S' ⊗[R] M') (S ⊗[R] M) (S' ⊗[R]  M') := inferInstance

/- TODO:  we need to prove that DividedPoweAlgebra.dpScalarExtensionEquiv
  is compatible with the graded structure and induces equivs componentwise -/
/-- The universal polynomial map (homogeneous of degree n) on a module -/
noncomputable
def gamma (n : ℕ) : PolynomialMap R M (DividedPowerAlgebra R M) where
  toFun' S _ _ := fun m ↦
    (DividedPowerAlgebra.dpScalarExtensionEquiv R S M).symm
      (DividedPowerAlgebra.dp S n m)
  isCompat' {S _ _ S' _ _} φ := by
    simp
    ext x
    revert n
    induction x using TensorProduct.induction_on with
    | zero =>
      intro n
      dsimp
      simp [dpScalarExtensionEquiv]
      simp only [dp_null]
      split_ifs
      · simp [AlgHom.map_one, Algebra.TensorProduct.one_def]
      · rw [AlgHom.map_zero, AlgHom.map_zero, LinearMap.map_zero]
    | tmul s m =>
      intro n
      simp [dpScalarExtensionEquiv]
      simp only [dpScalarExtensionInv_apply]
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_pow]
    | add x y hx hy =>
      intro n
      -- NOTE : maybe the definition of polynomial maps should involve
      -- the alghom map rather its coercion to linear map
      have : ⇑(LinearMap.rTensor (DividedPowerAlgebra R M) (AlgHom.toLinearMap φ))
        = ⇑(Algebra.TensorProduct.map φ (AlgHom.id R (DividedPowerAlgebra R M))) := rfl
      simp only [Function.comp_apply, map_add, this] at hx hy ⊢
      simp only [DividedPowerAlgebra.dp_add]
      rw [_root_.map_sum]
      rw [_root_.map_sum]
      rw [_root_.map_sum]
      apply Finset.sum_congr rfl
      rintro ⟨k, l⟩ _
      dsimp
      specialize hx k
      specialize hy l
      conv_rhs => rw [AlgEquiv.map_mul]
      rw [_root_.map_mul]
      rw [_root_.map_mul]
      simp_rw [hx, hy]

theorem gamma_toFun (n : ℕ) {S : Type*} [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (gamma R M n).toFun S m = (dpScalarExtensionEquiv R S M).symm (dp S n m) := sorry

theorem isHomogeneousOfDegree_gamma (n : ℕ) :
    PolynomialMap.IsHomogeneousOfDegree n (DividedPowerAlgebra.gamma R M n) := by
  intro S _ _ r sm
  simp only [gamma]-- , dpScalarExtensionEquiv, ofAlgHom_symm_apply]
  apply (dpScalarExtensionEquiv R S M).injective
  simp only [apply_symm_apply, LinearMapClass.map_smul]
  rw [dp_smul]

theorem gamma_mem_grade (n : ℕ) (S : Type*) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (gamma R M n).toFun S m ∈ LinearMap.range (LinearMap.lTensor S (grade R M n).subtype) := by
  revert n
  induction m using TensorProduct.induction_on with
  | zero =>
    intro n
    simp only [gamma_toFun, dp_null]
    split_ifs with h
    · rw [AlgEquiv.map_one, h]
      simp only [LinearMap.mem_range]
      use (1 : S) ⊗ₜ[R] ⟨(1 : DividedPowerAlgebra R M), one_mem R M⟩
      simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype]
      rw [Algebra.TensorProduct.one_def]
    · simp only [map_zero, zero_mem]
  | tmul s m =>
    intro n
    simp only [gamma_toFun, dpScalarExtensionEquiv]
    simp only [ofAlgHom_symm_apply]
    rw [dpScalarExtensionInv_apply]
    simp only [LinearMap.mem_range]
    use (s ^ n) ⊗ₜ[R] ⟨dp R n m, dp_mem_grade R M n m⟩
    simp only [LinearMap.lTensor_tmul, Submodule.coeSubtype]
  | add x y hx hy =>
    intro n
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
