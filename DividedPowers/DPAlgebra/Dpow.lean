import DividedPowers.DPAlgebra.Init
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.RatAlgebra
import DividedPowers.SubDPIdeal
import DividedPowers.IdealAdd
import DividedPowers.DPAlgebra.RobyLemma9
import DividedPowers.DPAlgebra.PolynomialMap
--import DividedPowers.ForMathlib.RingTheory.Ideal
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Construction of divided powers of tensor products of divided power algebras

## Main results

The two main constructions of this file are the following:

### Tensor products

Let `R`, `A`, `B` be commutative rings, with `Algebra R A` and `Algebra R B`,
given with divided power structures on ideals `I` and `J`.

- `on_tensorProduct_unique`: There is at most one divided power structure
on `A ⊗[R] B`, for the ideal `I ⊔ J`,
so that the canonical morphisms `A →ₐ[R] A ⊗[R] B` and `B →ₐ[R] A ⊗[R] B`
are dp-morphisms.

Such  a divided power struture doesn't always exist
(see counterexample in [Berthelot1974])

- It exists when `I` and `J` are `R`-augmentation ideals,
ie, there are sections `A ⧸ I →ₐ[R] A` and `B ⧸ J →ₐ[R] B`.

### Divided power algebra

Let `R` be a commutative ring, `M` an `R`-module.
We construct the unique divided power structure on `DividedPowerAlgebra R M`
for which `dpow n (DividedPower.linearEquivDegreeOne m) = dp n m` for any `m : M`,
where `linearEquivDegreeOne` is the `LinearEquiv`  from `M`
to the degree 1 part of `DividedPowerAlgebra R M`

- `on_dp_algebra_unique`: uniqueness of this structure

## Reference

* [Roby1965]

## Construction

The construction is highly non trivial and relies on a complicated process.
The uniqueness is clear, what is difficult is to prove the relevant
functional equations.
The result is banal if `R` is a ℚ-algebra and the idea is to lift `M`
to a free module over a torsion-free algebra.
Then the functional equations would hold by embedding everything into
the tensorization by ℚ.
Lifting `R` is banal (take a polynomial ring with ℤ-coefficients),
but `M` does not lift in general,
so one first has to lift `M` to a free module.
The process requires to know several facts regarding the divided power algebra:
- its construction commutes with base change (`DividedPowerAlgebra.dpScalarEquiv`).
- The graded parts of the divided power algebra of a free module are free.

Incidentally, there is no other proof in the litterature than the
paper [Roby1965].
This formalization would be the second one.

-/
noncomputable section

universe u v v₁ v₂ w

section sup

open Submonoid Submodule

theorem Submodule.mem_sup_iff_exists_add
  {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {M₁ M₂ : Submodule R M} (m : M) :
  m ∈ M₁ ⊔ M₂ ↔ ∃ m₁ ∈ M₁, ∃ m₂ ∈ M₂, m₁ + m₂ = m := by
  rw [← Submodule.mem_toAddSubmonoid (M₁ ⊔ M₂),
    Submodule.sup_toAddSubmonoid, AddSubmonoid.mem_sup]
  simp only [Submodule.mem_toAddSubmonoid]

end sup


section augmentation

open RingHom Ideal.Quotient Ideal TensorProduct Algebra.TensorProduct Function

end augmentation

section

variable (R : Type u) [CommRing R] [DecidableEq R]
  (M : Type v) [AddCommGroup M] [DecidableEq M] [Module R M]

variable (x : M) (n : ℕ)


open Finset MvPolynomial Ideal.Quotient

-- triv_sq_zero_ext
open Ideal

-- direct_sum
open RingQuot

namespace DividedPowerAlgebra

open DividedPowerAlgebra

/-- Lemma 2 of Roby 65. -/
theorem on_dp_algebra_unique (h h' : DividedPowers (augIdeal R M))
    (h1 : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    (h1' : ∀ (n : ℕ) (x : M), h'.dpow n (ι R M x) = dp R n x) : h = h' := by
  apply DividedPowers.dp_uniqueness_self h' h (augIdeal_eq_span R M)
  rintro n f ⟨q, hq : 0 < q, m, _, rfl⟩
  nth_rw 1 [← h1' q m]
  rw [← h1 q m, h.dpow_comp n (ne_of_gt hq) (ι_mem_augIdeal R M m),
    h'.dpow_comp n (ne_of_gt hq) (ι_mem_augIdeal R M m), h1 _ m, h1' _ m]
#align divided_power_algebra.on_dp_algebra_unique DividedPowerAlgebra.on_dp_algebra_unique

/-- Existence of divided powers on the augmentation ideal of an `R`-module `M`-/
def Condδ (R : Type u) [CommRing R] [DecidableEq R]
    (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∃ h : DividedPowers (augIdeal R M), ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x
#align divided_power_algebra.cond_δ DividedPowerAlgebra.Condδ

-- Universe constraint : one needs to have M in universe u
set_option linter.uppercaseLean3 false
/-- Existence, for every `R`-module, of divided powers on its divided power algebra -/
def CondD (R : Type u) [CommRing R] [DecidableEq R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M], ∀ [Module R M], Condδ R M
#align divided_power_algebra.cond_D DividedPowerAlgebra.CondD

end DividedPowerAlgebra

end

section Roby

-- Formalization of Roby 1965, section 8

open Finset MvPolynomial Ideal.Quotient Ideal RingQuot DividedPowers

namespace DividedPowerAlgebra

open DividedPowerAlgebra

section TensorProduct

open scoped TensorProduct

variable (A : Type u) (R : Type u) (S : Type u) [CommRing A] [CommRing R] [Algebra A R] [CommRing S] [Algebra A S]
  {I : Ideal R} {J : Ideal S} (hI : DividedPowers I) (hJ : DividedPowers J)

def i1 : R →ₐ[A] R ⊗[A] S :=
  Algebra.TensorProduct.includeLeft
#align divided_power_algebra.i_1 DividedPowerAlgebra.i1

def i2 : S →ₐ[A] R ⊗[A] S :=
  Algebra.TensorProduct.includeRight
#align divided_power_algebra.i_2 DividedPowerAlgebra.i2

variable {R S} (I J)

set_option linter.uppercaseLean3 false
def K : Ideal (R ⊗[A] S) :=
  I.map (i1 A R S) ⊔ J.map (i2 A R S)
#align divided_power_algebra.K DividedPowerAlgebra.K

variable {I J}

-- Lemma 1 : uniqueness of the dp structure on R ⊗ S for I + J
theorem on_tensorProduct_unique (hK hK' : DividedPowers (K A I J))
    (hIK : isDPMorphism hI hK (i1 A R S)) (hIK' : isDPMorphism hI hK' (i1 A R S))
    (hJK : isDPMorphism hJ hK (i2 A R S)) (hJK' : isDPMorphism hJ hK' (i2 A R S)) :
    hK = hK' := by
  apply eq_of_eq_on_ideal
  intro n x hx
  suffices x ∈ dpEqualizer hK hK' by exact ((mem_dpEqualizer_iff _ _).mp this).2 n
  suffices h_ss : K A I J ≤ dpEqualizer hK hK' by
    exact h_ss hx
  dsimp only [K]
  rw [sup_le_iff]
  constructor
  apply le_equalizer_of_dp_morphism hI (i1 A R S).toRingHom le_sup_left hK hK' hIK hIK'
  apply le_equalizer_of_dp_morphism hJ (i2 A R S).toRingHom le_sup_right hK hK' hJK hJK'
#align divided_power_algebra.on_tensor_product_unique DividedPowerAlgebra.on_tensorProduct_unique

/-- Existence of divided powers on the ideal of a tensor product
  of two divided power algebras -/
def Condτ (A : Type u) [CommRing A]
    {R : Type u} [CommRing R] [Algebra A R] {I : Ideal R} (hI : DividedPowers I)
    {S : Type u} [CommRing S] [Algebra A S] {J : Ideal S} (hJ : DividedPowers J) : Prop :=
  ∃ hK : DividedPowers (K A I J),
    isDPMorphism hI hK (i1 A R S) ∧ isDPMorphism hJ hK (i2 A R S)
#align divided_power_algebra.cond_τ DividedPowerAlgebra.Condτ

/-- Existence of divided powers on the ideal of a tensor product
  of any two divided power algebras (universalization of `Condτ`)-/
def CondT (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R], ∀ [Algebra A R], ∀ {I : Ideal R} (hI : DividedPowers I),
  ∀ (S : Type u) [CommRing S], ∀ [Algebra A S], ∀ {J : Ideal S} (hJ : DividedPowers J),
  Condτ A hI hJ
#align divided_power_algebra.cond_T DividedPowerAlgebra.CondT

end TensorProduct

section free

set_option linter.uppercaseLean3 false
/-- Existence of divided powers on the canonical ideal
  of a tensor product of divided power algebras
  which are free as modules -/
def CondTFree (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R], ∀ [Algebra A R], ∀ (_ : Module.Free A R),
    ∀ {I : Ideal R} (hI : DividedPowers I),
  ∀ (S : Type u) [CommRing S], ∀ [Algebra A S], ∀ (_ : Module.Free A S),
    ∀ {J : Ideal S} (hJ : DividedPowers J),
  Condτ A hI hJ
#align divided_power_algebra.cond_T_free DividedPowerAlgebra.CondTFree


/-- Existence, for any algebra with divided powers,
  of an over-algebra with divided powers which is free as a module -/
def CondQ (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R], ∀ [Algebra A R] (I : Ideal R) (hI : DividedPowers I),
  ∃ (T : Type u) (_ : CommRing T), ∃ (_ : Algebra A T),
    ∃ (_ : Module.Free A T) (f : T →ₐ[A] R)
      (J : Ideal T) (hJ : DividedPowers J) (_ : isDPMorphism hJ hI f),
  I = J.map f ∧ Function.Surjective f
#align divided_power_algebra.cond_Q DividedPowerAlgebra.CondQ

/-- Existence, for any split algebra with divided powers,
  of an over-algebra with split divided powers
  which is free as a module -/
def CondQSplit (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R],
  ∀ [Algebra A R] (I : Ideal R) (hI : DividedPowers I)
    (R₀ : Subalgebra A R) (_ : IsCompl (Subalgebra.toSubmodule R₀) (I.restrictScalars A)),
  ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T)
    (J : Ideal T) (hJ : DividedPowers J)
    (T₀ : Subalgebra A T) (_ : IsCompl (Subalgebra.toSubmodule T₀) (J.restrictScalars A))
    (f : T →ₐ[A] R),
    J.map f = I ∧ T₀.map f = R₀ ∧ Function.Surjective f ∧ isDPMorphism hJ hI f ∧ Module.Free A T

end free

section Proofs

variable {R : Type u} [CommRing R]

open DividedPowerAlgebra

open scoped TensorProduct

-- Roby, lemma 3
set_option linter.uppercaseLean3 false
/-- Any divided power structure on the divided power algebra
  makes the canonical morphisms to a divided power ring
  a DP morphism -/
theorem cond_D_uniqueness [DecidableEq R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (h : DividedPowers (augIdeal R M))
    (hh : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    {S : Type*} [CommRing S] [Algebra R S] {J : Ideal S} (hJ : DividedPowers J)
    (f : M →ₗ[R] S) (hf : ∀ m, f m ∈ J) :
    isDPMorphism h hJ (DividedPowerAlgebra.lift hJ f hf) := by
  classical
  constructor
  · rw [augIdeal_eq_span]
    rw [Ideal.map_span]
    rw [Ideal.span_le]
    intro s
    rintro ⟨a, ⟨n, hn : 0 < n, m, _, rfl⟩, rfl⟩
    simp only [AlgHom.coe_toRingHom, SetLike.mem_coe]
    rw [liftAlgHom_apply_dp]
    apply hJ.dpow_mem (ne_of_gt hn) (hf m)
  · intro n a ha
    --    simp only [alg_hom.coe_to_ring_hom],
    apply symm
    rw [(dp_uniqueness h hJ (lift hJ f hf) (augIdeal_eq_span R M) _ _) n a ha]
    · rintro a ⟨q, hq : 0 < q, m, _, rfl⟩
      simp only [AlgHom.coe_toRingHom, liftAlgHom_apply_dp]
      exact hJ.dpow_mem (ne_of_gt hq) (hf m)
    · rintro n a ⟨q, hq : 0 < q, m, _, rfl⟩
      simp only [AlgHom.coe_toRingHom, liftAlgHom_apply_dp]
      rw [hJ.dpow_comp n (ne_of_gt hq) (hf m),← hh q m,
        h.dpow_comp n (ne_of_gt hq) (ι_mem_augIdeal R M m), _root_.map_mul, map_natCast]
      apply congr_arg₂ _ rfl
      rw [hh]; rw [liftAlgHom_apply_dp]
#align divided_power_algebra.cond_D_uniqueness DividedPowerAlgebra.cond_D_uniqueness

example {A R S : Type*} [CommSemiring A]
  [CommSemiring R] [Algebra A R]
  [Semiring S] [Algebra A S] [Algebra R S]
  [IsScalarTower A R S] :
  R →ₐ[A] S where
    toRingHom := algebraMap R S
    commutes' := fun r ↦ by
      simp [IsScalarTower.algebraMap_eq A R S]


-- We open a namespace to privatize the complicated construction
namespace roby4

variable (A : Type u) [CommRing A] [DecidableEq A]

open Classical

/- The goal of this section is to establish [Roby1963, Lemme 4]
`T_free_and_D_to_Q`, that under the above assumptions, `CondQ A` holds.
It involves a lifting construction -/

variable (S : Type u) [CommRing S] [Algebra A S]
  {I : Ideal S} (hI : DividedPowers I)
  (S₀ : Subalgebra A S)
  (hIS₀ : IsCompl (Subalgebra.toSubmodule S₀) (I.restrictScalars A))

-- We construct MvPolynomial S₀ A = A[S₀] →ₐ[A] S₀
instance : Algebra (MvPolynomial S₀ A) S₀ :=
  RingHom.toAlgebra (MvPolynomial.aeval id).toRingHom

theorem algebraMap_eq :
    algebraMap (MvPolynomial S₀ A) S₀ = (MvPolynomial.aeval id).toRingHom :=
  rfl -- RingHom.algebraMap_toAlgebra (algebraMap (MvPolynomial S₀ A) S₀)

example : IsScalarTower A (MvPolynomial S₀ A) S₀ := inferInstance

/- instance : IsScalarTower A (MvPolynomial S A) S := {
  smul_assoc := fun a r s => by
    simp only [Algebra.smul_def, algebraMap_eq]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, _root_.map_mul, AlgHom.commutes]
    rw [← mul_assoc] } -/

variable {S} (I) in
def f : (I →₀ A) →ₗ[A] S :=
  (Basis.constr (Finsupp.basisSingleOne) A) (fun i ↦ (i : S))

variable {S} (I) in
theorem f_mem_I (p) : f A I p ∈ I := by
  suffices LinearMap.range (f A I) ≤ Submodule.restrictScalars A I by
    apply this
    simp only [LinearMap.mem_range, exists_apply_eq_apply]
  simp only [f, Basis.constr_range, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, SetLike.coe_mem]

variable  (condTFree : CondTFree A) (condD : CondD A)

variable (hM : DividedPowers (augIdeal A (I →₀ A)))
  (hM_eq : ∀ n x, hM.dpow n ((ι A (I →₀ A)) x) = dp A n x)

instance hdpM_free : Module.Free A (DividedPowerAlgebra A (I →₀ A)) :=
  DividedPowerAlgebra.toModule_free _ _

instance hR_free : Module.Free A (MvPolynomial S A) :=
  Module.Free.of_basis (MvPolynomial.basisMonomials _ _)

def hR := dividedPowersBot (MvPolynomial S A)

variable (I) in
theorem condτ : Condτ A (dividedPowersBot (MvPolynomial S₀ A)) hM := by
  apply condTFree
  infer_instance
  infer_instance

def Φ : DividedPowerAlgebra A (I →₀ A) →ₐ[A] S :=
  DividedPowerAlgebra.lift hI (f A I) (f_mem_I _ _)

def dpΦ : dpMorphism hM hI := by
  apply dpMorphismFromGens hM hI (augIdeal_eq_span _ _) (f := (Φ A S hI).toRingHom)
  · rw [Ideal.map_le_iff_le_comap, augIdeal_eq_span, span_le]
    rintro x ⟨n, hn, b, _, rfl⟩
    simp only [Set.mem_setOf_eq] at hn
    simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, mem_comap, RingHom.coe_coe]
    simp only [Φ, liftAlgHom_apply_dp]
    exact hI.dpow_mem (ne_of_gt hn) (f_mem_I A I b)
  · rintro n x ⟨m, hm, b, _, rfl⟩
    simp only [Set.mem_setOf_eq] at hm
    simp only [Φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, liftAlgHom_apply_dp]
    rw [← hM_eq, hM.dpow_comp, hI.dpow_comp]
    simp only [_root_.map_mul, map_natCast]
    apply congr_arg₂ _ rfl
    rw [hM_eq, liftAlgHom_apply_dp]
    exact ne_of_gt hm
    exact f_mem_I A I b
    exact ne_of_gt hm
    apply ι_mem_augIdeal

-- We consider `(MvPolynomial S₀ A) ⊗[A] DividedPowerAlgebra A (I →₀ A) → S`
def Ψ : MvPolynomial S₀ A ⊗[A] DividedPowerAlgebra A (I →₀ A) →ₐ[A] S :=
  Algebra.TensorProduct.productMap
    ((Subalgebra.val S₀).comp (IsScalarTower.toAlgHom A (MvPolynomial S₀ A) S₀))
    (Φ A S hI)

theorem Ψ_surjective : Function.Surjective (Ψ A S hI S₀) := by
  rw [← Algebra.range_top_iff_surjective _, eq_top_iff]
  intro s _
  obtain ⟨s₀, hs₀, s₁, hs₁, rfl⟩ := Submodule.exists_add_eq_of_codisjoint (hIS₀.codisjoint) s
  apply Subalgebra.add_mem
  · -- case s₀
    use (X ⟨s₀, hs₀⟩) ⊗ₜ[A] 1
    simp only [Ψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.productMap_apply_tmul, AlgHom.coe_comp, Subalgebra.coe_val,
      IsScalarTower.coe_toAlgHom', algebraMap_eq, Function.comp_apply, aeval_X, id_eq, map_one,
      mul_one]
  · -- case s₁
    use 1 ⊗ₜ[A] (ι A _ (Finsupp.single ⟨s₁, hs₁⟩ 1))
    simp only [Ψ, Φ, f, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, lift_ι_apply, one_mul]
    simp only [Basis.constr_apply, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply, zero_smul,
      Finsupp.sum_single_index, one_smul]

variable (I) in
theorem K_eq_span :
    K A (⊥ : Ideal (MvPolynomial S₀ A)) (augIdeal A (↥I →₀ A))
      = span (Set.image2 (fun n a ↦ 1 ⊗ₜ[A] dp A n a) {n | 0 < n} Set.univ) := by
  simp [K, i1, i2]
  rw [augIdeal_eq_span, Ideal.map_span]
  simp only [Algebra.TensorProduct.includeRight_apply, Set.image_image2]

def dpΨ : dpMorphism (condτ A S I S₀ condTFree hM).choose hI := by
  apply dpMorphismFromGens (condτ A S I S₀ condTFree hM).choose hI
    (f := (Ψ A S hI S₀).toRingHom) (K_eq_span A S I S₀)
  · simp only [AlgHom.toRingHom_eq_coe, K, Ideal.map_bot, i2, ge_iff_le,
      bot_le, sup_of_le_right, map_le_iff_le_comap]
    rw [augIdeal_eq_span, span_le]
    rintro _ ⟨n, hn, b, _, rfl⟩
    simp only [Set.mem_setOf_eq] at hn
    simp only [SetLike.mem_coe, mem_comap, Algebra.TensorProduct.includeRight_apply,
      RingHom.coe_coe]
    simp only [Ψ, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    apply (dpΦ A S hI hM hM_eq).ideal_comp
    apply Ideal.mem_map_of_mem
    exact dp_mem_augIdeal A (I →₀ A) hn b
  · rintro n _ ⟨m, hm, b, _, rfl⟩
    simp only [Set.mem_setOf_eq] at hm
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    erw [← ((condτ A S I S₀ condTFree hM).choose_spec.2).map_dpow]
    simp only [Ψ, i2, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    erw [(dpΦ A S hI hM hM_eq).dpow_comp]
    · rfl
    all_goals
      apply dp_mem_augIdeal _ _ hm

/-- `MvPolynomial.C` as an `AlgHom`. -/
@[simps! apply]
def _root_.MvPolynomial.CAlgHom {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
 {σ : Type*} : A →ₐ[R] MvPolynomial σ A where
  toRingHom := C
  commutes' _ := rfl


-- Roby, lemma 4
theorem _root_.DividedPowerAlgebra.T_free_and_D_to_QSplit :
    CondQSplit A := by
  intro S _ _ I hI S₀ hIS₀
  let M := I →₀ A
  let R := MvPolynomial S₀ A
  obtain ⟨hM, hM_eq⟩ := condD M
  haveI hdpM_free : Module.Free A (DividedPowerAlgebra A M) := by
    apply DividedPowerAlgebra.toModule_free
  haveI hR_free : Module.Free A R :=
    Module.Free.of_basis (MvPolynomial.basisMonomials _ _)
  -- We consider `R ⊗[A] DividedPowerAlgebra A M` as a comm ring and an A-algebra
  let T := R ⊗[A] DividedPowerAlgebra A M
  use T, by infer_instance, by infer_instance
  /- We need to add the fact that `R ⊗ DividedPowerAlgebra A M``
     is pregraduated in the sense of Roby
     The ideal is `K A ⊥ (augIdeal A M)`,
     that is, `R ⊗[A] augIdeal A M``
     hence it is a direct factor of R ⊗[A] A
     (At this point, I wonder why one cannot prove
      that the divided power algebra of a free module
      has divided powers --- the relations come from combinatorics.)
      and then return DividedPowerAlgebra R (I →₀ R).)
     R ⊗[A] A maps to S
     DividedPowerAlgebra A M mapso I
     and the first term should map to S₀
     so the construction needs to be refined


     -/
  let idK : Ideal T := K A ⊥ (augIdeal A M)
  have hidK : idK = Ideal.map Algebra.TensorProduct.includeRight (augIdeal A M) := by
    simp only [K, Ideal.map_bot, i2, ge_iff_le, bot_le, sup_of_le_right, idK]
  use idK
  let hK : DividedPowers idK := (condτ A S I S₀ condTFree hM).choose
  use hK
  have : MvPolynomial S₀ A →ₐ[A] MvPolynomial S₀ A ⊗[A] DividedPowerAlgebra A M := by
    apply Algebra.TensorProduct.includeLeft
  use Subalgebra.restrictScalars A (⊥ : Subalgebra R T)
  have isaugΓ : IsCompl
      (Subalgebra.toSubmodule (⊥ : Subalgebra A _))
      ((augIdeal A M).restrictScalars A) := by
    sorry
  /- have : IsCompl
    (Subalgebra.toSubmodule (Subalgebra.restrictScalars A ⊥)) (Submodule.restrictScalars A idK) := by
    simp only [hidK]
    have := Algebra.TensorProduct.lTensor_isCompl A R (S := DividedPowerAlgebra A M) (I := augIdeal A M) isaugΓ
    sorry


  have : Subalgebra A (MvPolynomial S₀ A ⊗[A] DividedPowerAlgebra A M) :=
    Subalgebra.map Algebra.TensorProduct.includeLeft ⊤
  -- ???
  have hisCompl : IsCompl
      (Subalgebra.toSubmodule (Subalgebra.map Algebra.TensorProduct.includeLeft ⊤ : Subalgebra A (MvPolynomial S₀ A ⊗[A] DividedPowerAlgebra A M)))
      (Submodule.restrictScalars A (K A ⊥ (augIdeal A M))) := by
    simp only [Algebra.map_top, K, Ideal.map_bot, i2, ge_iff_le, bot_le, sup_of_le_right]

    sorry
  use sorry
  use Subalgebra.map Algebra.TensorProduct.includeLeft ⊤
  refine ?_
-/
  -- the 0 part of our algebra


  use sorry -- it is a complement
  use Ψ A S hI S₀
  constructor
  · sorry
    /- refine le_antisymm ?_ (dpΨ A S hI S₀ condTFree hM hM_eq).ideal_comp
    intro i hi
    let m : M := Finsupp.single ⟨i, hi⟩ 1
    have : i = Ψ A S hI (Algebra.TensorProduct.includeRight (ι A M m)) :=  by
      simp [m, Ψ, Φ, f, Basis.constr_apply]
    rw [this]
    apply Ideal.mem_map_of_mem
    apply Ideal.mem_sup_right
    apply Ideal.mem_map_of_mem
    apply ι_mem_augIdeal
    sorry -/
  constructor
  · sorry -- Ψ maps the 0 part to S₀
  constructor
  · apply Ψ_surjective A S hI S₀ hIS₀
  constructor
  · exact (dpΨ A S hI S₀ condTFree hM hM_eq).isDPMorphism
  infer_instance -- tensor product of free modules is free


end roby4


example {A : Type*} [CommRing A] (a : A) (n : ℕ) : n • a = n * a := by refine' nsmul_eq_mul n a

lemma _root_.Ideal.map_toRingHom (A R S : Type*) [CommSemiring A]
    [Semiring R] [Algebra A R] [Semiring S] [Algebra A S] (f : R →ₐ[A] S)
    (I : Ideal R) : Ideal.map f I = Ideal.map f.toRingHom I := rfl


/- In Roby, all PD-algebras A considered are of the form A₀ ⊕ A₊,
where A₊ is the PD-ideal. In other words, the PD-ideal is an augmentation ideal.
Moreover, PD-morphisms map A₀ to B₀ and A₊ to B₊,
so that their kernel is a direct sum K₀ ⊕ K₊

Roby's framework is stated in terms of `pre-graded algebras`,
namely graded algebras by the monoid {⊥, ⊤} with carrier set `Fin 2`
(with multiplication, ⊤ = 0 and ⊥ = 1)

Most of the paper works in greater generality, as noted by Berthelot,
but not all the results hold in general.
Berthelot gives an example (1.7) of a tensor product of algebras
with divided power ideals whose natural ideal does not have compatible
divided powers.

[Berthelot, 1.7.1] gives the explicit property that holds for tensor products.
For an `A`-algebra `R` and `I : Ideal R`, one assumes the
existence of `R₀ : Subalgebra A R` such that `R = R₀ ⊕ I` as an `I`-module.
Equivalently, the map `R →ₐ[A] R ⧸ I` has a left inverse.

In lemma 6, we have two surjective algebra morphisms
 f : R →+* R',  g : S →+* S'
and we consider the induced surjective morphism fg : R ⊗ S →+* R' ⊗ S'
R has a PD-ideal I,  R' has a PD-ideal I',
S has a PD-ideal J,  S' has a PD-ideal J'
with assumptions that I' = map f I and J' = map g J,
with quotient PD structures

Lemma 5 has proved that  fg.ker = (f.ker ⊗ 1) ⊔ (1 ⊗ g.ker)

The implicit hypothesis in lemma 6 is that f is homogeneous,
ie, maps R₊ = I to R'₊ = J and R₀ to R'₀, and same for g

In the end, Roby applies his proposition 4 which we
apparently haven't formalized and make use of yet another definition,
namely of a `divised ideal` :
Up to the homogeneous condition, this is exactly that `K ⊓ I` is a sub-pd-ideal.
The proof of proposition goes by using that
`Ideal.span (s ∩ ↑I) = Ideal.span s ⊓ I`
if `s` consists of homogeneous elements.

So we assume the `roby` condition in the statement, in the hope
that will be possible to prove it each time we apply cond_τ_rel
-/

-- Roby, lemma 6
theorem condτ_rel (A : Type u) [CommRing A] {R S R' S' : Type u} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra A R] [Algebra A S] [Algebra A R'] [Algebra A S']
    (f : R →ₐ[A] R') (hf : Function.Surjective f) {I : Ideal R} (hI : DividedPowers I)
    {I' : Ideal R'} (hI' : DividedPowers I') (hf' : isDPMorphism hI hI' f) (hI'I : I' = I.map f)
    (g : S →ₐ[A] S') (hg : Function.Surjective g) {J : Ideal S} (hJ : DividedPowers J)
    {J' : Ideal S'} (hJ' : DividedPowers J') (hg' : isDPMorphism hJ hJ' g) (hJ'J : J' = J.map g)
    (roby :
      RingHom.ker (Algebra.TensorProduct.map f g) ⊓ K A I J =
        Ideal.map (Algebra.TensorProduct.includeLeft (S := A)) (RingHom.ker f ⊓ I)
          ⊔ Ideal.map (Algebra.TensorProduct.includeRight) (RingHom.ker g ⊓ J))
    (hRS : Condτ A hI hJ) : Condτ A hI' hJ' := by
  obtain ⟨hK, hK_pd⟩ := hRS
  simp only [Condτ]
  let fg := Algebra.TensorProduct.map f g
  have s_fg : Function.Surjective fg := TensorProduct.map_surjective hf hg
  have hK_map : K A I' J' = (K A I J).map fg := by
    simp only [K, fg, hI'I, hJ'J]
    rw [Ideal.map_sup]
    apply congr_arg₂
    all_goals
      simp only [Ideal.map_toRingHom, Ideal.map_map]
      apply congr_arg₂ _ _ rfl
      ext x
      simp only [i1, i2, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hK'_pd : isSubDPIdeal hK (RingHom.ker fg ⊓ K A I J) := by
    rw [roby]
    apply isSubDPIdeal_sup
    exact isSubDPIdeal_map hI hK hK_pd.1 _ (isSubDPIdeal_ker hI hI' hf')
    exact isSubDPIdeal_map hJ hK hK_pd.2 _ (isSubDPIdeal_ker hJ hJ' hg')
  rw [hK_map]
  use DividedPowers.Quotient.OfSurjective.dividedPowers hK s_fg hK'_pd
  constructor
  · -- hI'.is_pd_morphism hK' ↑(i_1 A R' S')
    constructor
    · rw [← hK_map]
      rw [Ideal.map_le_iff_le_comap]; intro a' ha'
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_left; apply Ideal.mem_map_of_mem; exact ha'
    · intro n a' ha'
      simp only [hI'I, Ideal.mem_map_iff_of_surjective f hf] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      simp only [i1, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeLeft_apply]
      rw [← map_one g, ← Algebra.TensorProduct.map_tmul]
      rw [← AlgHom.coe_toRingHom f, hf'.2 n a ha, RingHom.coe_coe]
      rw [← Algebra.TensorProduct.map_tmul]
      erw [Quotient.OfSurjective.dpow_apply hK s_fg hK'_pd]
      apply congr_arg
      exact hK_pd.1.2 n a ha
      apply Ideal.mem_sup_left
      apply Ideal.mem_map_of_mem _ ha
  · -- hJ'.is_pd_morphism hK' ↑(i_2 A R' S')
    constructor
    · rw [← hK_map]
      rw [Ideal.map_le_iff_le_comap]; intro a' ha'
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_right; apply Ideal.mem_map_of_mem; exact ha'
    · intro n a' ha'
      simp only [hJ'J, Ideal.mem_map_iff_of_surjective g hg] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      simp only [i2, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
      suffices ∀ y : S, fg.toRingHom (1 ⊗ₜ[A] y) = 1 ⊗ₜ[A] g y by
        rw [← this]
        rw [Quotient.OfSurjective.dpow_apply hK s_fg]
        have that := hg'.2 n a ha
        simp only [AlgHom.coe_toRingHom] at that ; rw [that]
        rw [← this]
        apply congr_arg
        simp only [← Algebra.TensorProduct.includeRight_apply]
        exact hK_pd.2.2 n a ha
        apply Ideal.mem_sup_right
        apply Ideal.mem_map_of_mem _ ha
      intro x
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
        fg]
#align divided_power_algebra.cond_τ_rel DividedPowerAlgebra.condτ_rel

-- Roby, Proposition 4
example (A : Type*) [CommRing A] (R : Type*) [CommRing R] [Algebra A R]
    (I : Ideal R) (R₀ : Subalgebra A R)
    (hsplit : IsCompl (Subalgebra.toSubmodule R₀) (I.restrictScalars A))
    (J : Ideal R) (F₀ : Set R₀) (FI : Set I)
    (hJ : J = Submodule.span R (F₀ ∪ FI : Set R)) :
    J.restrictScalars A
      = (Subalgebra.toSubmodule R₀ ⊓ J.restrictScalars A)
          ⊔ (I.restrictScalars A ⊓ J.restrictScalars A) := by
  rcases hsplit with ⟨hd, hc⟩
  simp only [codisjoint_iff] at hc
  simp only [Submodule.disjoint_def, Subalgebra.mem_toSubmodule,
    Submodule.restrictScalars_mem] at hd
  refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  intro x hx
  simp only [hJ, SetLike.coe_sort_coe, Submodule.restrictScalars_mem] at hx
  apply Submodule.span_induction hx (p := fun x ↦ x ∈ _)
  · rintro _ (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · apply Submodule.mem_sup_left
      simp only [Submodule.mem_inf, Subalgebra.mem_toSubmodule, SetLike.coe_mem,
        Submodule.restrictScalars_mem, true_and]
      rw [hJ]
      apply Submodule.subset_span
      apply Set.mem_union_left
      simp only [SetLike.coe_sort_coe, Set.mem_image, SetLike.coe_eq_coe, exists_eq_right, hx]
    · apply Submodule.mem_sup_right
      simp only [hJ, SetLike.coe_sort_coe, submodule_span_eq, Submodule.mem_inf,
        Submodule.restrictScalars_mem, SetLike.coe_mem, true_and]
      apply Submodule.subset_span
      apply Set.mem_union_right
      simp only [Set.mem_image, SetLike.coe_eq_coe, exists_eq_right, hy]
  · exact zero_mem _
  · exact fun x y hx hy ↦ add_mem hx hy
  · intro a x hx
    simp only [← Submodule.add_eq_sup, ← SetLike.mem_coe, Submodule.coe_add] at hx
    rw [Submodule.coe_add] at hx
    simp only [SetLike.mem_coe] at hx


    have ha : a ∈ Subalgebra.toSubmodule R₀ + Submodule.restrictScalars A I := by
      change a ∈ Subalgebra.toSubmodule R₀ ⊔ _
      rw [hc]
      exact trivial
    simp only [Submodule.add_eq_sup] at hx
    obtain ⟨x₀, hx₀, y, hy, rfl⟩ := hx

    suffices ∃ a₀ ∈ R₀, ∃ b ∈ I, a = a₀ + b by
      obtain ⟨a₀, ha₀, b, hb, rfl⟩ := this
      rw [add_smul]
      apply add_mem
      · sorry
      · sorry
    sorry

theorem Ideal.map_coe_toRingHom
  {A : Type*} [CommRing A] {R S : Type*} [CommRing R] [CommRing S]
  [Algebra A R] [Algebra A S] (f : R →ₐ[A] S)
  (I : Ideal R) : Ideal.map f I = Ideal.map f.toRingHom I := by
  rfl

-- Roby, lemma 7
theorem condQ_and_condTFree_imply_condT (A : Type*) [CommRing A]
    (hQ : CondQ A) (hT_free : CondTFree A) : CondT A := by
  intro R' _ _ I' hI' S' _ _ J' hJ'
  simp only [CondQ] at hQ
  obtain ⟨R, _, _, hR_free, f, I, hI, hfDP, hfI, hf⟩ := hQ R' I' hI'
  obtain ⟨S, _, _, hS_free, g, J, hJ, hgDP, hgJ, hg⟩ := hQ S' J' hJ'
  apply condτ_rel A f hf hI hI' hfDP hfI g  hg hJ hJ' hgDP hgJ
  · rw [Algebra.TensorProduct.map_ker _ _ hf hg]
  -- Il faudra appliquer la Proposition 4 de Roby,
  -- en s'étant assuré que les algèbres R et S sont scindées
  /-
    have : ∃ (R₀ : Subalgebra A R),
      IsCompl (Subalgebra.toSubmodule R₀) (I.restrictScalars A)
      ∧ RingHom.ker f = (RingHom.ker f ⊓ I) ⊔
        (Ideal.map R₀.val (Ideal.comap R₀.val (RingHom.ker f))) := sorry
    obtain ⟨R₀, hR₀, hkerf⟩ := this
    have : ∃ (S₀ : Subalgebra A S),
      IsCompl (Subalgebra.toSubmodule S₀) (J.restrictScalars A)
      ∧ RingHom.ker g = (RingHom.ker g ⊓ J) ⊔
        (Ideal.map S₀.val (Ideal.comap S₀.val (RingHom.ker g))) := sorry
    obtain ⟨S₀, hS₀, hkerg⟩ := this
    conv_lhs => rw [hkerf, hkerg]
    rw [Ideal.map_sup, Ideal.map_sup, K]
    simp only [i1, i2, Ideal.map_coe_toRingHom]
    simp only [Ideal.map_map]
    simp only [sup_assoc]

  -- still inconclusive
  -- on paper, one split `R = R₀ ⊕ I`, `S = S₀ ⊕ J`,
  -- this decomposes `R ⊗ S` as a sum of 4 terms
  -- one needs to explain that `ker f = (ker f ∩ R₀) ⊕ (ker f ∩ I)
  -- and similarly for `ker g`,
  -- which is supposed to follow from `hkerf`, if well formulated
  --
  -/
    sorry
  · apply hT_free
    exact hR_free
    exact hS_free
#align divided_power_algebra.cond_Q_and_cond_T_free_imply_cond_T
  DividedPowerAlgebra.condQ_and_condTFree_imply_condT

-- Roby, lemma 8
theorem condT_and_condD_imply_cond_D' (A : Type*) [CommRing A] [DecidableEq A]
    (hT : CondT A) (hD : CondD A)
    (R : Type*) [CommRing R]  [DecidableEq R] [Algebra A R] :
    CondD R :=
  sorry
#align divided_power_algebra.cond_T_and_cond_D_imply_cond_D'
  DividedPowerAlgebra.condT_and_condD_imply_cond_D'

-- Roby, lemma 9 is in roby9
-- Roby, lemma 10
theorem condT_implies_cond_T'_free (A : Type*) [CommRing A] (R : Type*) [CommRing R] [Algebra A R]
    (hA : CondT A) : CondTFree R :=
  sorry
#align divided_power_algebra.cond_T_implies_cond_T'_free
  DividedPowerAlgebra.condT_implies_cond_T'_free

-- Roby, lemma 11
theorem condTFree_int : CondTFree ℤ :=
  sorry
#align divided_power_algebra.cond_T_free_int DividedPowerAlgebra.condTFree_int

-- Roby, lemma 12
theorem condD_int : CondD ℤ :=
  sorry
#align divided_power_algebra.cond_D_int DividedPowerAlgebra.condD_int

theorem condQ_int : CondQSplit ℤ :=
  T_free_and_D_to_QSplit ℤ condTFree_int condD_int
#align divided_power_algebra.cond_Q_int DividedPowerAlgebra.condQ_int

theorem condT_int : CondT ℤ :=
  sorry
  -- condQ_and_condTFree_imply_condT ℤ condQ_int condTFree_int
#align divided_power_algebra.cond_T_int DividedPowerAlgebra.condT_int

theorem condD_holds (A : Type*) [CommRing A] [DecidableEq A] : CondD A :=
  condT_and_condD_imply_cond_D' ℤ condT_int condD_int A
#align divided_power_algebra.cond_D_holds DividedPowerAlgebra.condD_holds

theorem condTFree_holds (A : Type*) [CommRing A] : CondTFree A :=
  condT_implies_cond_T'_free ℤ A condT_int
#align divided_power_algebra.cond_T_free_holds DividedPowerAlgebra.condTFree_holds

theorem condQ_holds (A : Type*) [CommRing A] [DecidableEq A] : CondQ A :=
  sorry
  -- T_free_and_D_to_Q A (condTFree_holds A) (condD_holds A)
#align divided_power_algebra.cond_Q_holds DividedPowerAlgebra.condQ_holds

theorem condT_holds (A : Type*) [CommRing A] [DecidableEq A] : CondT A :=
  condQ_and_condTFree_imply_condT A (condQ_holds A) (condTFree_holds A)
#align divided_power_algebra.cond_T_holds DividedPowerAlgebra.condT_holds

end Proofs

-- Old names
theorem roby_δ (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M]
    [Module A M] : DividedPowerAlgebra.Condδ A M :=
  condD_holds A M
#align divided_power_algebra.roby_δ DividedPowerAlgebra.roby_δ

set_option linter.uppercaseLean3 false
theorem roby_D (A : Type*) [CommRing A] [DecidableEq A] : DividedPowerAlgebra.CondD A :=
  condD_holds A
#align divided_power_algebra.roby_D DividedPowerAlgebra.roby_D

theorem roby_τ (A R S : Type u) [CommRing A] [DecidableEq A] [CommRing R] [Algebra A R]
    [CommRing S] [Algebra A S]
    {I : Ideal R} {J : Ideal S} (hI : DividedPowers I) (hJ : DividedPowers J) : Condτ A hI hJ :=
  condT_holds A R hI S hJ
#align divided_power_algebra.roby_τ DividedPowerAlgebra.roby_τ

theorem roby_T (A : Type*) [CommRing A] [DecidableEq A] : CondT A :=
  condT_holds A
#align divided_power_algebra.roby_T DividedPowerAlgebra.roby_T

open DividedPowerAlgebra

-- namespace divided_power_algebra
-- Part of Roby65 Thm 1
def dividedPowers' (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M]
    [Module A M] : DividedPowers (augIdeal A M) :=
  (roby_D A M).choose
#align divided_power_algebra.divided_powers' DividedPowerAlgebra.dividedPowers'

theorem dpow_ι (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M] [Module A M]
    (x : M) (n : ℕ) : dpow (dividedPowers' A M) n (ι A M x) = dp A n x :=
  (roby_D A M).choose_spec n x
#align divided_power_algebra.dpow_ι DividedPowerAlgebra.dpow_ι

theorem dp_comp (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M] [Module A M]
    (x : M) {n : ℕ} (m : ℕ) (hn : n ≠ 0) :
    dpow (dividedPowers' A M) m (dp A n x) = ↑(mchoose m n) * dp A (m * n) x := by
  erw [← (roby_D A M).choose_spec, dpow_comp _ m hn (ι_mem_augIdeal A M x), dpow_ι]
#align divided_power_algebra.dp_comp DividedPowerAlgebra.dp_comp

theorem roby_theorem_2 (R : Type u) [CommRing R]  [DecidableEq R]
    (M : Type u) [AddCommGroup M] [Module R M]
    {A : Type u} [CommRing A] [Algebra R A] {I : Ideal A} (hI : DividedPowers I)
    {φ : M →ₗ[R] A} (hφ : ∀ m, φ m ∈ I) :
    isDPMorphism (dividedPowers' R M) hI (DividedPowerAlgebra.lift hI φ hφ) := by
  apply cond_D_uniqueness
  intro m n
  rw [dpow_ι]
#align divided_power_algebra.roby_theorem_2 DividedPowerAlgebra.roby_theorem_2

-- TODO: fix the last two theorems
theorem lift'_eq_dp_lift (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (S : Type w) [CommRing S] [DecidableEq S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) :
    ∃ hφ : ∀ m, ((ι S N).restrictScalars R).comp f m ∈ augIdeal S N,
      LinearMap.lift R S f =
        DividedPowerAlgebra.lift (dividedPowers' S N)
          (((ι S N).restrictScalars R).comp f) hφ := by
  have hφ : ∀ m, ((ι S N).restrictScalars R).comp f m ∈ augIdeal S N := by
    intro m
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, ι_mem_augIdeal S N (f m)]
  use hφ
  apply DividedPowerAlgebra.ext
  intro n m
  simp only [liftAlgHom_apply_dp, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply]
  simp only [LinearMap.liftAlgHom_dp]
  simp only [ι, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dp_comp _ _ _ _ Nat.one_ne_zero]
  simp only [mchoose_one', Nat.cast_one, mul_one, one_mul]

theorem roby_prop_8 (R : Type u) [DecidableEq R] [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    (S : Type u) [DecidableEq S] [CommRing S] [Algebra R S]
    {N : Type u} [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) :
    isDPMorphism (dividedPowers' R M) (dividedPowers' S N) (LinearMap.lift R S f) := by
  obtain ⟨hφ, phφ'⟩ := lift'_eq_dp_lift R S f
  convert roby_theorem_2 R M (dividedPowers' S N) hφ
#align divided_power_algebra.roby_prop_8 DividedPowerAlgebra.roby_prop_8

end DividedPowerAlgebra

end Roby


#exit

-- Possibly useless results that in anycase should be elsewhere
-- possibly in AugmentationIdeal

section


variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]
variable (p q : Submodule R E)

variable {p q}

open LinearMap Submodule

theorem _root_.Submodule.linearProjOfIsCompl_comp_subtype' (h : IsCompl p q) :
    (linearProjOfIsCompl p q h).comp q.subtype = 0 :=
  LinearMap.ext <| linearProjOfIsCompl_apply_right h

end

example (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    (N : Type*) [AddCommGroup N] [Module A N]
    (N' N'' : Submodule A N) (hN : IsCompl N' N'') :
  IsCompl
    (LinearMap.range (LinearMap.lTensor M N'.subtype))
    (LinearMap.range (LinearMap.lTensor M N''.subtype)) := by
  let ι : Submodule A N → Submodule A (M ⊗[A] N) :=
    fun N' ↦ LinearMap.range (LinearMap.lTensor M N'.subtype)
  have hsup : ∀ N₁ N₂, ι (N₁ ⊔ N₂) = ι N₁ ⊔ ι N₂ := sorry
  have hinf : ∀ N₁ N₂, ι (N₁ ⊓ N₂) = ι N₁ ⊓ ι N₂ := sorry
  exact {
    disjoint := by
      rw [disjoint_iff, ← hinf, disjoint_iff.mp hN.disjoint]
      simp only [ι, LinearMap.range_eq_bot]
      convert LinearMap.lTensor_zero M
      sorry
    codisjoint := by
      rw [codisjoint_iff, ← hsup, codisjoint_iff.mp hN.codisjoint]
      simp only [ι, LinearMap.range_eq_top]
      apply LinearMap.lTensor_surjective
      rw [← LinearMap.range_eq_top, Submodule.range_subtype] }

theorem _root_.Submodule.isCompl_lTensor_of_isCompl
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    (N : Type*) [AddCommGroup N] [Module A N]
    (N' N'' : Submodule A N) (hN : IsCompl N' N'') :
  IsCompl
    (LinearMap.range (LinearMap.lTensor M N'.subtype))
    (LinearMap.range (LinearMap.lTensor M N''.subtype)) :=
  let p := Submodule.linearProjOfIsCompl _ _ hN
  have hp : LinearMap.ker p = N'' := by
    simp only [p, Submodule.linearProjOfIsCompl_ker]
  have hpM : LinearMap.ker (LinearMap.lTensor M p) = LinearMap.range (LinearMap.lTensor M N''.subtype) := by
    rw [← LinearMap.exact_iff]
    apply lTensor_exact M
    simp only [LinearMap.exact_iff, hp, Submodule.range_subtype]
    simp only [p, ← LinearMap.range_eq_top, Submodule.linearProjOfIsCompl_range]
  let p' := Submodule.linearProjOfIsCompl _ _ hN.symm
  have hp' : LinearMap.ker p' = N' := by
    simp only [p', Submodule.linearProjOfIsCompl_ker]
  have hp'M : LinearMap.ker (LinearMap.lTensor M p') = LinearMap.range (LinearMap.lTensor M N'.subtype) := by
    rw [← LinearMap.exact_iff]
    apply lTensor_exact M
    simp only [LinearMap.exact_iff, hp', Submodule.range_subtype]
    simp only [p', ← LinearMap.range_eq_top, Submodule.linearProjOfIsCompl_range]
  let q : N →ₗ[A] N := N'.subtype.comp p + N''.subtype.comp p'
  have hq : q = LinearMap.id := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Submodule.coeSubtype,
      Function.comp_apply, LinearMap.id_coe, id_eq, q]
    rw [Submodule.linear_proj_add_linearProjOfIsCompl_eq_self]

  { disjoint := by
      rw [Submodule.disjoint_def]
      intro x h h'
      have hp : LinearMap.lTensor M p x = 0 := by
        rw [← LinearMap.mem_ker, hpM]
        exact h'
      have hp' : LinearMap.lTensor M p' x = 0 := by
        rw [← LinearMap.mem_ker, hp'M]
        exact h
      rw [← LinearMap.id_apply x (R := A), ← LinearMap.lTensor_id, ← hq]
      simp only [LinearMap.lTensor_add, LinearMap.lTensor_comp,
        LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        hp, map_zero, hp', add_zero, q]
    codisjoint := by
      rw [codisjoint_iff]
      rw [eq_top_iff]
      intro x _
      rw [← LinearMap.lTensor_id_apply M _ x, ← hq]
      simp only [LinearMap.lTensor_add, LinearMap.add_apply, q]
      simp only [LinearMap.lTensor_comp, LinearMap.comp_apply]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_left
        apply LinearMap.mem_range_self
      · apply Submodule.mem_sup_right
        apply LinearMap.mem_range_self }

theorem _root_.LinearMap.baseChange_isCompl (R : Type*) [CommRing R] [Algebra A R]
  (M : Type*) [AddCommGroup M] [Module A M]
  {M₁ M₂ : Submodule A M} (hM : IsCompl M₁ M₂) :
  IsCompl
    (LinearMap.range (LinearMap.baseChange R (M₁.subtype)))
    (LinearMap.range (LinearMap.baseChange R (M₂.subtype))) := by
  let p := Submodule.linearProjOfIsCompl _ _ hM
  have hp : LinearMap.ker p = M₂ := by
    simp only [p, Submodule.linearProjOfIsCompl_ker]
  have hpM : LinearMap.ker (LinearMap.baseChange R p)
    = LinearMap.range (LinearMap.baseChange R M₂.subtype) := by
    rw [← LinearMap.exact_iff]
    change Function.Exact (LinearMap.lTensor R _) (LinearMap.lTensor R _)
    apply lTensor_exact
    simp only [LinearMap.exact_iff, hp, Submodule.range_subtype]
    simp only [p, ← LinearMap.range_eq_top, Submodule.linearProjOfIsCompl_range]
  let p' := Submodule.linearProjOfIsCompl _ _ hM.symm
  have hp' : LinearMap.ker p' = M₁ := by
    simp only [p', Submodule.linearProjOfIsCompl_ker]
  have hp'M : LinearMap.ker (LinearMap.baseChange R p')
    = LinearMap.range (LinearMap.baseChange R M₁.subtype) := by
    rw [← LinearMap.exact_iff]
    apply lTensor_exact
    simp only [LinearMap.exact_iff, hp', Submodule.range_subtype]
    simp only [p', ← LinearMap.range_eq_top, Submodule.linearProjOfIsCompl_range]
  let q : M →ₗ[A] M := M₁.subtype.comp p + M₂.subtype.comp p'
  have hq : q = LinearMap.id := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Submodule.coeSubtype,
      Function.comp_apply, LinearMap.id_coe, id_eq, q]
    rw [Submodule.linear_proj_add_linearProjOfIsCompl_eq_self]
  have hdisjoint : Disjoint
    (LinearMap.range (LinearMap.baseChange R (M₁.subtype)))
    (LinearMap.range (LinearMap.baseChange R (M₂.subtype))) := by
      rw [Submodule.disjoint_def]
      intro x h h'
      have hp : LinearMap.lTensor R p x = 0 := by
        rw [← LinearMap.mem_ker]
        rw [← hpM] at h'
        exact h'
      have hp' : LinearMap.lTensor R p' x = 0 := by
        rw [← LinearMap.mem_ker]
        rw [← hp'M] at h
        exact h
      rw [← LinearMap.id_apply x (R := A), ← LinearMap.lTensor_id, ← hq]
      simp only [LinearMap.lTensor_add, LinearMap.lTensor_comp,
        LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        hp, map_zero, hp', add_zero, q]
  have hcodisjoint : Codisjoint
    (LinearMap.range (LinearMap.baseChange R (M₁.subtype)))
    (LinearMap.range (LinearMap.baseChange R (M₂.subtype))) := by
      rw [codisjoint_iff]
      rw [eq_top_iff]
      intro x _
      rw [← LinearMap.lTensor_id_apply R _ x, ← hq]
      simp only [LinearMap.lTensor_add, LinearMap.add_apply, q]
      simp only [LinearMap.lTensor_comp, LinearMap.comp_apply]
      apply Submodule.add_mem
      · apply Submodule.mem_sup_left
        rw [← LinearMap.baseChange_eq_ltensor]
        apply LinearMap.mem_range_self
      · apply Submodule.mem_sup_right
        rw [← LinearMap.baseChange_eq_ltensor]
        apply LinearMap.mem_range_self
  exact {
    disjoint :=  hdisjoint
    codisjoint := hcodisjoint }

/-- The base change of an algebra with an augmentation ideal -/
theorem _root_.Algebra.TensorProduct.lTensor_isCompl
  (R : Type*) [CommRing R] [Algebra A R]
  (S : Type*) [CommRing S] [Algebra A S]
  {I : Ideal S}
  (hI : IsCompl (Subalgebra.toSubmodule (⊥ : Subalgebra A S)) (I.restrictScalars A)) :
  IsCompl
    (Subalgebra.toSubmodule (⊥ : Subalgebra R (R ⊗[A] S)))
    (Submodule.restrictScalars R (Ideal.map Algebra.TensorProduct.includeRight I)) := by
  convert LinearMap.baseChange_isCompl A R S hI
  · ext x
    simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range,
      Algebra.TensorProduct.includeLeft_apply, LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      use x ⊗ₜ[A] (1 : (⊥ : Subalgebra A S))
      rfl
    · rintro ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | tmul r s =>
        rcases s with ⟨s, hs⟩
        simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hs
        obtain ⟨a, rfl⟩ := hs
        simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype, Algebra.mem_bot]
        use a • r
        simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
        rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        simp only [map_add]
        exact Subalgebra.add_mem _ hx hy
      | zero =>
        simp only [LinearMap.map_zero]
        apply Subalgebra.zero_mem
  · ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
    unfold Ideal.map
    constructor
    · intro hx
      apply Submodule.span_induction hx (p := fun x ↦ ∃ y, _ = x)
      · rintro _ ⟨s, hs, rfl⟩; use (1 : R) ⊗ₜ[A] ⟨s, hs⟩; rfl
      · use 0; simp only [map_zero]
      · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; use x + y; simp only [map_add]
      · rintro a _ ⟨x, rfl⟩
        induction x using TensorProduct.induction_on with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul r b =>
          induction a using TensorProduct.induction_on with
          | zero =>
            use 0
            simp only [map_zero, LinearMap.baseChange_tmul, Submodule.coeSubtype, smul_eq_mul,
              zero_mul]
          | tmul u v =>
            simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype, smul_eq_mul,
              Algebra.TensorProduct.tmul_mul_tmul]
            use (u * r) ⊗ₜ[A] (v • b)
            simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype]
            rfl
          | add u v hu hv =>
            obtain ⟨x, hx⟩ := hu
            obtain ⟨y, hy⟩ := hv
            use x + y
            simp only [map_add, add_smul, hx, hy]
        | add x x' hx hx' =>
          obtain ⟨y, hx⟩ := hx
          obtain ⟨y', hx'⟩ := hx'
          use y + y'
          simp only [map_add, hx, hx', smul_add]
    · rintro ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        apply Submodule.zero_mem
      | tmul r b =>
        simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype,
          Algebra.TensorProduct.includeRight_apply]
        suffices r ⊗ₜ[A] (b : S) = (r ⊗ₜ[A] (1 : S)) • ((1 : R) ⊗ₜ[A] (b : S)) by
          rw [this]
          apply Submodule.smul_mem
          apply Ideal.subset_span
          use b
          constructor
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, SetLike.coe_mem]
          rfl
        simp only [Submodule.coe_restrictScalars, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
      | add x y hx hy =>
        simp only [map_add]
        apply Submodule.add_mem _ hx hy

section restrictScalars

variable
    {A : Type*} [CommSemiring A]
    {R : Type*} [Semiring R] [Algebra A R]
    {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower A R M]
    (M₁ M₂ : Submodule R M)

theorem Submodule.sup_restrictScalars :
   (M₁ ⊔ M₂).restrictScalars A = M₁.restrictScalars A ⊔ (M₂.restrictScalars A) := by
  apply Submodule.toAddSubmonoid_injective
  simp only [Submodule.toAddSubmonoid_restrictScalars, Submodule.sup_toAddSubmonoid]

theorem Submodule.codisjoint_restrictScalars_iff :
    Codisjoint (M₁.restrictScalars A) (M₂.restrictScalars A) ↔
      Codisjoint M₁ M₂ := by
  simp only [codisjoint_iff, ← Submodule.sup_restrictScalars, Submodule.restrictScalars_eq_top_iff]

theorem Submodule.disjoint_restrictScalars_iff :
    Disjoint (M₁.restrictScalars A) (M₂.restrictScalars A) ↔
      Disjoint M₁ M₂ := by
  simp only [Submodule.disjoint_def, Submodule.restrictScalars_mem]

theorem Submodule.isCompl_restrictScalars_iff  :
    IsCompl (M₁.restrictScalars A) (M₂.restrictScalars A) ↔ IsCompl M₁ M₂ := by
  simp only [isCompl_iff, Submodule.disjoint_restrictScalars_iff, Submodule.codisjoint_restrictScalars_iff]

theorem Subalgebra.toSubmodule_restrictScalars_eq
    {R : Type*} [CommSemiring R] [Algebra A R]
    {S : Type*} [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    (S' : Subalgebra R S) :
    Subalgebra.toSubmodule (Subalgebra.restrictScalars A S') = S'.toSubmodule.restrictScalars A :=
  rfl

end restrictScalars

/-- The base change of an algebra with an augmentation ideal -/
theorem _root_.Algebra.TensorProduct.lTensor_isCompl'
    {R : Type*} [CommRing R] [Algebra A R]
    {S : Type*} [CommRing S] [Algebra A S]
    {I : Ideal S}
    (hI : IsCompl (Subalgebra.toSubmodule (⊥ : Subalgebra A S)) (I.restrictScalars A)) :
    IsCompl
      (Subalgebra.toSubmodule ((⊥ : Subalgebra R (R ⊗[A] S)).restrictScalars A))
      (Submodule.restrictScalars A (Ideal.map Algebra.TensorProduct.includeRight I)) := by
  rw [Subalgebra.toSubmodule_restrictScalars_eq]

  have : Submodule.restrictScalars A (Ideal.map Algebra.TensorProduct.includeRight I)
    = Submodule.restrictScalars A
      (Submodule.restrictScalars R
        (Ideal.map Algebra.TensorProduct.includeRight I : Ideal (R ⊗[A] S)) : Submodule R (R ⊗[A] S)) := rfl
  rw [this]
  rw [Submodule.isCompl_restrictScalars_iff]
  convert LinearMap.baseChange_isCompl A R S hI
  · ext x
    simp only [Algebra.toSubmodule_bot, Submodule.mem_one, Algebra.TensorProduct.algebraMap_apply,
      Algebra.id.map_eq_id, RingHom.id_apply, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      have : 1 ∈ (1 : Submodule A S) := by
        simp only [Submodule.mem_one]
        use 1
        rw [map_one]
      use y ⊗ₜ[A] ⟨1, this⟩
      rfl
    · rintro ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero =>
        use 0
        simp only [TensorProduct.zero_tmul, LinearMap.map_zero]
      | tmul r s =>
        rcases s with ⟨s, hs⟩
        simp only [Submodule.mem_one] at hs
        obtain ⟨a, rfl⟩ := hs
        use a • r
        simp only [TensorProduct.smul_tmul]
        congr
        simp only [Submodule.coeSubtype, Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        obtain ⟨x', hx⟩ := hx
        obtain ⟨y', hy⟩ := hy
        use x' + y'
        simp only [TensorProduct.add_tmul, hx, hy, map_add]
  · ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
    constructor
    · intro hx
      apply Submodule.span_induction hx (p := fun x ↦ ∃ y, (LinearMap.baseChange R (Submodule.subtype (Submodule.restrictScalars A I))) y = x )
      · rintro x ⟨s, hs, rfl⟩; use 1 ⊗ₜ[A] ⟨s, hs⟩; rfl
      · use 0; simp only [map_zero]
      · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; use x + y; simp only [map_add]
      · rintro a _ ⟨x, rfl⟩
        induction x using TensorProduct.induction_on with
        | zero => use 0; simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul r s =>
          induction a using TensorProduct.induction_on with
          | zero =>
            use 0
            simp only [map_zero, LinearMap.baseChange_tmul,
              Submodule.coeSubtype, smul_eq_mul, zero_mul]
          | tmul u v =>
            use (u * r) ⊗ₜ[A] (v • s)
            simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype, smul_eq_mul,
              Algebra.TensorProduct.tmul_mul_tmul]
            rw [Submodule.coe_smul, smul_eq_mul]
          | add u v hu hv =>
            obtain ⟨x, hx⟩ := hu
            obtain ⟨y, hy⟩ := hv
            use x + y
            rw [LinearMap.map_add, add_smul, hx, hy]
        | add x y hx hy =>
          obtain ⟨x', hx⟩ := hx
          obtain ⟨y', hy⟩ := hy
          use x' + y'
          simp only [map_add, hx, smul_eq_mul, hy, mul_add]
    · rintro ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, Submodule.zero_mem]
      | tmul r s => sorry
      | add x y hx hy =>
        simp only [map_add]
        exact Ideal.add_mem _ hx hy
/-  · ext x
    simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range,
      Algebra.TensorProduct.includeLeft_apply, LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      use x ⊗ₜ[A] (1 : (⊥ : Subalgebra A S))
      rfl
    · rintro ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | tmul r s =>
        rcases s with ⟨s, hs⟩
        simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hs
        obtain ⟨a, rfl⟩ := hs
        simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype, Algebra.mem_bot]
        use a • r
        simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
        rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
      | add x y hx hy =>
        simp only [map_add]
        exact Subalgebra.add_mem _ hx hy
      | zero =>
        simp only [map_zero]
        apply Subalgebra.zero_mem
  · ext x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
    unfold Ideal.map
    constructor
    · intro hx
      apply Submodule.span_induction hx (p := fun x ↦ ∃ y, _ = x)
      · rintro _ ⟨s, hs, rfl⟩
        use (1 : R) ⊗ₜ[A] ⟨s, hs⟩
        rfl
      · use 0
        simp only [map_zero]
      · rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        use x + y
        simp only [map_add]
      · rintro a _ ⟨x, rfl⟩
        induction x using TensorProduct.induction_on with
        | zero =>
          use 0
          simp only [map_zero, smul_eq_mul, mul_zero]
        | tmul r b =>
          induction a using TensorProduct.induction_on with
          | zero =>
            use 0
            simp only [map_zero, LinearMap.baseChange_tmul, Submodule.coeSubtype, smul_eq_mul,
              zero_mul]
          | tmul u v =>
            simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype, smul_eq_mul,
              Algebra.TensorProduct.tmul_mul_tmul]
            use (u * r) ⊗ₜ[A] (v • b)
            simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype]
            rfl
          | add u v hu hv =>
            obtain ⟨x, hx⟩ := hu
            obtain ⟨y, hy⟩ := hv
            use x + y
            simp only [map_add, add_smul, hx, hy]
        | add x x' hx hx' =>
          obtain ⟨y, hx⟩ := hx
          obtain ⟨y', hx'⟩ := hx'
          use y + y'
          simp only [map_add, hx, hx', smul_add]
    · rintro ⟨x, rfl⟩
      induction x using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero]
        apply Submodule.zero_mem
      | tmul r b =>
        simp only [LinearMap.baseChange_tmul, Submodule.coeSubtype,
          Algebra.TensorProduct.includeRight_apply]
        suffices r ⊗ₜ[A] (b : S) = (r ⊗ₜ[A] (1 : S)) • ((1 : R) ⊗ₜ[A] (b : S)) by
          rw [this]
          apply Submodule.smul_mem
          apply Ideal.subset_span
          use b
          constructor
          simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, SetLike.coe_mem]
          rfl
        simp only [Submodule.coe_restrictScalars, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
      | add x y hx hy =>
        simp only [map_add]
        apply Submodule.add_mem _ hx hy
-/
