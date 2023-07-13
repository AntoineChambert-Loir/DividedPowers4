import Oneshot.ForMathlib.RingTheory.TensorProduct
import Mathbin.RingTheory.Ideal.QuotientOperations
import Mathbin.Algebra.Algebra.Subalgebra.Basic

-- import ...generalisation.generalisation_linter
-- import ...generalisation.generalisation_linter
open scoped TensorProduct

local notation:100 M " ⊗[" R "] " N:100 => TensorProduct R M N

-- The goal is to prove lemma 9 in Roby (1965)
section RingHom

theorem RingHom.ker_eq_ideal_iff {A B : Type _} [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) : f.ker = I ↔ ∃ h : I ≤ f.ker, Function.Injective (Ideal.Quotient.lift I f h) :=
  by
  constructor
  · intro hI; use le_of_eq hI.symm
    apply RingHom.lift_injective_of_ker_le_ideal
    simp only [hI, le_refl]
  · rintro ⟨hI, h⟩
    simp only [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift f hI,
      Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h 
    exact le_antisymm h hI
#align ring_hom.ker_eq_ideal_iff RingHom.ker_eq_ideal_iff

end RingHom

section AlgHom

theorem AlgHom.ker_eq_ideal_iff {R A B : Type _} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (I : Ideal A) :
    RingHom.ker f = I ↔ ∃ h : I ≤ RingHom.ker f, Function.Injective (Ideal.Quotient.liftₐ I f h) :=
  by
  have : RingHom.ker f = RingHom.ker f.to_ring_hom; rfl
  constructor
  · intro hI; use le_of_eq hI.symm
    suffices : Function.Injective (Ideal.Quotient.lift I f.to_ring_hom (le_of_eq hI.symm))
    intro x y hxy; apply this
    simpa only [Ideal.Quotient.liftₐ_apply] using hxy
    apply RingHom.lift_injective_of_ker_le_ideal
    rw [← hI, ← this]; exact le_refl _
  · rintro ⟨hI, h⟩
    rw [this]; rw [RingHom.ker_eq_ideal_iff]
    rw [this] at hI ; use hI
    intro x y hxy
    apply h
    simpa only [Ideal.Quotient.liftₐ_apply] using hxy
#align alg_hom.ker_eq_ideal_iff AlgHom.ker_eq_ideal_iff

end AlgHom

variable (R : Type _) [CommRing R] (S : Type _) [CommRing S]

variable (M : Type _) [CommRing M] [Algebra R M] [Algebra S M] (N : Type _) [CommRing N]
  [Algebra R N] [Algebra S N]

variable [Algebra R S] [IsScalarTower R S M] [IsScalarTower R S N]

-- [tensor_product.compatible_smul R S M N]
open Algebra.TensorProduct TensorProduct

def φ : M ⊗[R] N →ₐ[R] M ⊗[S] N :=
  Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft.restrictScalars R)
    (Algebra.TensorProduct.includeRight.restrictScalars R)
#align φ φ

theorem φ_apply (m : M) (n : N) : φ R S M N (m ⊗ₜ[R] n) = m ⊗ₜ[S] n := by
  simp only [φ, product_map_apply_tmul, AlgHom.coe_restrictScalars', include_left_apply,
    include_right_apply, tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
#align φ_apply φ_apply

theorem φ_surjective : Function.Surjective (φ R S M N) :=
  by
  intro z
  apply TensorProduct.induction_on z
  use 0; simp only [map_zero]
  intro m n; use m ⊗ₜ n; simp only [φ_apply]
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; use x + y; simp only [map_add]
#align φ_surjective φ_surjective

def kerφ : Ideal (M ⊗[R] N) :=
  Ideal.span ((fun r : S => (r • (1 : M)) ⊗ₜ[R] (1 : N) - (1 : M) ⊗ₜ[R] (r • (1 : N))) '' ⊤)
#align kerφ kerφ

example : N →ₐ[R] M ⊗[R] N :=
  includeRight

example : N →ₐ[R] M ⊗[R] N :=
  includeRight

example : N →ₐ[S] M ⊗[S] N :=
  includeRight

def ψLeft : M →ₐ[S] M ⊗[R] N ⧸ kerφ R S M N :=
  {
    ((Ideal.Quotient.mkₐ S (kerφ R S M N)).restrictScalars R).comp
      Algebra.TensorProduct.includeLeft with
    commutes' := fun s =>
      by
      simp only [AlgHom.toFun_eq_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
        Function.comp_apply, include_left_apply]
      simp only [Algebra.algebraMap_eq_smul_one]
      suffices : (s • (1 : M)) ⊗ₜ[R] (1 : N) = s • 1
      rw [this, AlgHom.map_smul, AlgHom.map_one]
      rfl }
#align ψ_left ψLeft

-- ψ_left' R S M N }
def ψRight : N →ₐ[S] M ⊗[R] N ⧸ kerφ R S M N :=
  { (Ideal.Quotient.mkₐ R (kerφ R S M N)).comp includeRight with
    commutes' := fun s =>
      by
      simp only [AlgHom.toFun_eq_coe, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        Function.comp_apply, include_right_apply]
      simp only [Algebra.algebraMap_eq_smul_one]
      rw [← (Ideal.Quotient.mk (kerφ R S M N)).map_one, ← Ideal.Quotient.mkₐ_eq_mk S, ←
        AlgHom.map_smul]
      simp only [Ideal.Quotient.mkₐ_eq_mk]
      apply symm
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨s, Set.mem_univ s, rfl⟩ }
#align ψ_right ψRight

def ψ : M ⊗[S] N →ₐ[S] M ⊗[R] N ⧸ kerφ R S M N :=
  productMap (ψLeft R S M N) (ψRight R S M N)
#align ψ ψ

theorem ψ_apply (m : M) (n : N) : ψ R S M N (m ⊗ₜ[S] n) = Ideal.Quotient.mk _ (m ⊗ₜ[R] n) :=
  by
  simp only [ψ, ψLeft, ψRight]
  simp only [AlgHom.toFun_eq_coe, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
    Ideal.Quotient.mkₐ_eq_mk, product_map_apply_tmul, AlgHom.coe_mks, Function.comp_apply,
    include_left_apply, include_right_apply]
  rw [← RingHom.map_mul]
  simp only [tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
#align ψ_apply ψ_apply

theorem kerφ_eq : (φ R S M N).toRingHom.ker = kerφ R S M N :=
  by
  suffices h : kerφ R S M N ≤ RingHom.ker (φ R S M N).toRingHom
  rw [RingHom.ker_eq_ideal_iff]
  use h
  apply Function.HasLeftInverse.injective
  --  apply function.bijective.injective,
  --  rw function.bijective_iff_has_inverse,
  use ψ R S M N
  --   split,
  · -- left_inverse
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [AlgHom.toRingHom_eq_coe, Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom]
    apply TensorProduct.induction_on y
    simp only [RingHom.map_zero, AlgHom.map_zero]
    intro m n; simp only [ψ_apply, φ_apply]
    intro x y hx hy
    simp only [RingHom.map_add, AlgHom.map_add, ← Ideal.Quotient.mkₐ_eq_mk, hx, hy]
  -- { -- right_inverse  sorry }
  -- h
  simp only [kerφ]
  rw [Ideal.span_le]
  intro z hz
  simp only [Set.top_eq_univ, Set.image_univ, Set.mem_range] at hz 
  obtain ⟨r, rfl⟩ := hz
  simp only [SetLike.mem_coe]
  simp only [RingHom.sub_mem_ker_iff]
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  simp only [φ_apply]
  simp only [TensorProduct.tmul_smul]
  rfl
#align kerφ_eq kerφ_eq

