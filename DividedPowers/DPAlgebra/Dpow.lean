
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.DPAlgebra.PolynomialMap
import DividedPowers.SubDPIdeal
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # The universal divided power algebra

## Main results

The two main constructions of this file are the following:

### Tensor products

Let `R`, `A`, `B` be commutative rings, with `Algebra R A` and `Algebra R B` and with divided
power structures on ideals `I` and `J`, respectively.

- `on_tensorProduct_unique` : There is at most one divided power structure
on the ideal `I ⊔ J` of `A ⊗[R] B` so that the canonical morphisms `A →ₐ[R] A ⊗[R] B` and
`B →ₐ[R] A ⊗[R] B` are dp-morphisms.

Such a divided power structure doesn't always exist (see counterexample in [Berthelot1974, 1.7])
-- TODO : add it

However, it always exists when `I` and `J` are `R`-augmentation ideals, i. e., when there are
sections `A ⧸ I →ₐ[R] A` and `B ⧸ J →ₐ[R] B`.

### Divided power algebra

Let `R` be a commutative ring, `M` an `R`-module.
We construct the unique divided power structure on `DividedPowerAlgebra R M` for which
`dpow n (ι R M m) = dp n m` for any `m : M`, where `ι R M` is the `LinearEquiv` from `M`
to the degree 1 part of `DividedPowerAlgebra R M`.

- `onDPAlgebra_unique`: uniqueness of this structure.

## Reference

* [Roby1965]

## Construction

The construction is highly non trivial and relies on a complicated process.
The uniqueness is clear, what is difficult is to prove the relevant functional equations.
The result is banal if `R` is a `ℚ`-algebra and the idea is to lift `M` to a free module over a
torsion-free algebra. Then the functional equations would hold by embedding everything into
the tensorization by `ℚ`.
Lifting `R` is banal (take a polynomial ring with `ℤ`-coefficients), but `M` does not lift in
general, so one first has to lift `M` to a free module.
The process requires to know several facts regarding the divided power algebra:
- Its construction commutes with base change (see `dpScalarExtensionEquiv`).
- The graded parts of the divided power algebra of a free module are free.

Incidentally, there is no other proof in the literature than the paper [Roby1965].
This formalization would be the second one.

-/
noncomputable section

universe u v v₁ v₂ w uA uR uS uM


--TODO
/- section Proposition1

variable {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R] {R₀ : Subalgebra A R} {I : Ideal R}
  (hIR₀ : IsAugmentation R₀ I) (hI : DividedPowers I)

--TODO
/- theorem proposition1 (F₀ : Set R₀) (FI : Set I) :
  isSubDPAlgebra A (Algebra.adjoin A ⊥ ((F₀ : Set R) ∪ (FI : Set R))) ↔
    sorry := sorry -/

end Proposition1 -/

namespace DividedPowerAlgebra

-- Formalization of Roby 1965, section 8
section Roby_section8

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

variable (x : M) (n : ℕ)

open DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

/-- Lemma 2 of Roby 65 : there is at most one divided power structure on the augmentation ideal
  of `DividedPowerAlgebra R M` such that `∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x`. -/
theorem onDPAlgebra_unique [DecidableEq R] (h h' : DividedPowers (augIdeal R M))
    (h1 : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    (h1' : ∀ (n : ℕ) (x : M), h'.dpow n (ι R M x) = dp R n x) : h = h' := by
  apply DividedPowers.unique_from_gens_self h' h (augIdeal_eq_span R M)
  rintro n f ⟨q, hq : 0 < q, m, _, rfl⟩
  nth_rw 1 [← h1' q m]
  rw [← h1 q m, h.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m),
    h'.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m), h1 _ m, h1' _ m]

/-- Existence of divided powers on the augmentation ideal of an `R`-module `M`. -/
def Condδ (R : Type u) [CommRing R] [DecidableEq R]
    (M : Type u) [AddCommGroup M] [Module R M] : Prop :=
  ∃ h : DividedPowers (augIdeal R M), ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x

-- Universe constraint : one needs to have `R` and `M` in the same universe `u`.
/-- Existence, for every `R`-module, of divided powers on the augmentation ideal of its
  divided power algebra. -/
def CondD (R : Type u) [CommRing R] [DecidableEq R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], Condδ R M

-- TODO : at the end , universalize

section TensorProduct

open scoped TensorProduct

/-- The ideal `K := I + J` in the tensor product `R ⊗[A] S`. -/
def K (A : Type uA) [CommRing A] {R : Type uR} [CommRing R] [Algebra A R] (I : Ideal R)
    {S : Type uS} [CommRing S] [Algebra A S] (J : Ideal S) : Ideal (R ⊗[A] S) :=
  I.map (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S)
    ⊔ J.map Algebra.TensorProduct.includeRight

variable (A : Type u) [CommRing A] {R : Type u} [CommRing R] [Algebra A R]
  {I : Ideal R} (hI : DividedPowers I) {S : Type u} [CommRing S] [Algebra A S]
  {J : Ideal S} (hJ : DividedPowers J)

/-- Lemma 1 : There is a unique divided power structure on the ideal `I + J` of `R ⊗ S` for
  which the canonical morphism `R →ₐ[A] R ⊗[A] S` and `S →ₐ[A] R ⊗[A] S` are divided power
  morphisms. -/
theorem on_tensorProduct_unique (hK : DividedPowers (K A I J))
    (hIK : IsDPMorphism hI hK (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S))
    (hJK : IsDPMorphism hJ hK (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S))
    (hK' : DividedPowers (K A I J))
    (hIK' : IsDPMorphism hI hK' (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S))
    (hJK' : IsDPMorphism hJ hK' (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S)) :
    hK = hK' := by
  apply eq_of_eq_on_ideal
  intro n x hx
  suffices x ∈ dpEqualizer hK hK' from ((mem_dpEqualizer_iff _ _).mp this).2 n
  suffices h_ss : K A I J ≤ dpEqualizer hK hK' from h_ss hx
  exact sup_le_iff.mpr ⟨le_equalizer_of_dp_morphism hI _ le_sup_left hK hK' hIK hIK',
    le_equalizer_of_dp_morphism hJ _ le_sup_right hK hK' hJK hJK'⟩


/-- Existence of divided powers on the ideal `I + J` of a tensor product of two divided power
  algebras. -/
def Condτ (A : Type u) [CommRing A] {R : Type u} [CommRing R] [Algebra A R]
    {I : Ideal R} (hI : DividedPowers I) {S : Type u} [CommRing S] [Algebra A S]
    {J : Ideal S} (hJ : DividedPowers J) : Prop :=
  ∃ hK : DividedPowers (K A I J),
    IsDPMorphism hI hK (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S)
    ∧ IsDPMorphism hJ hK (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S)

/- Existence of divided powers on the ideal of a tensor product
  of any two divided power algebras (universalization of `Condτ`)
def CondT (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] {I : Ideal R} (hI : DividedPowers I)
    (S : Type u) [CommRing S] [Algebra A S] {J : Ideal S} (hJ : DividedPowers J), Condτ A hI hJ -/

/-- Existence of divided powers on the ideal of a tensor product
  of any two *split* divided power algebras (universalization of `Condτ`).
  Note that this differs from the definition in Roby, who does not required the algebras
  to be split. -/
def CondT (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] {I : Ideal R} (hI : DividedPowers I)
    {R₀ : Subalgebra A R} (_ : I.IsAugmentation R₀) (S : Type u) [CommRing S] [Algebra A S]
    {J : Ideal S} (hJ : DividedPowers J) {S₀ : Subalgebra A S} (_ : J.IsAugmentation S₀),
    Condτ A hI hJ

end TensorProduct

section free

/-- Existence of divided powers on the canonical ideal of a tensor product of divided power
  algebras which are free as modules -/
def CondTFree (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] [Module.Free A R] {I : Ideal R}
    (hI : DividedPowers I) (S : Type u) [CommRing S] [Algebra A S] [Module.Free A S]
    {J : Ideal S} (hJ : DividedPowers J), Condτ A hI hJ

/-- Existence, for any algebra with divided powers,
  of an over-algebra with divided powers which is free as a module -/
def CondQ' (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] (I : Ideal R) (hI : DividedPowers I),
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T) (_ : Module.Free A T) (f : T →ₐ[A] R)
      (J : Ideal T) (hJ : DividedPowers J),
      IsDPMorphism hJ hI f ∧ I = J.map f ∧ Function.Surjective f

/-- Existence, for any split algebra with divided powers, of an over-algebra with split divided
  powers which is free as a module -/
def CondQ (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra A R] (I : Ideal R) (hI : DividedPowers I)
    (R₀ : Subalgebra A R) (_ : Ideal.IsAugmentation R₀ I),
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T) (J : Ideal T) (hJ : DividedPowers J)
      (T₀ : Subalgebra A T) (_ : Ideal.IsAugmentation T₀ J) (f : T →ₐ[A] R),
      J.map f = I ∧ T₀.map f = R₀ ∧ Function.Surjective f ∧ IsDPMorphism hJ hI f ∧ Module.Free A T

end free

end Roby_section8

-- Formalization of Roby 1965, section 9
section Roby_section9

open DividedPowerAlgebra DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

variable {R : Type uR} [CommRing R]

open scoped TensorProduct

-- Roby, lemma 3
/-- Any divided power structure on the divided power algebra makes the canonical morphisms to a
  divided power ring a DP morphism. -/
theorem cond_D_uniqueness [DecidableEq R] {M : Type uM} [AddCommGroup M] [Module R M]
    (h : DividedPowers (augIdeal R M)) (hh : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    {S : Type uS} [CommRing S] [Algebra R S] {J : Ideal S} (hJ : DividedPowers J)
    (f : M →ₗ[R] S) (hf : ∀ m, f m ∈ J) :
    IsDPMorphism h hJ (DividedPowerAlgebra.lift hJ f hf) := by
  classical
  constructor
  · rw [augIdeal_eq_span, map_span, span_le]
    rintro s ⟨a, ⟨n, hn : 0 < n, m, _, rfl⟩, rfl⟩
    rw [AlgHom.coe_toRingHom, SetLike.mem_coe, lift_apply_dp]
    exact hJ.dpow_mem (ne_of_gt hn) (hf m)
  · intro n a ha
    rw [(unique_from_gens h hJ (augIdeal_eq_span R M) _ _) a ha]
    · rintro a ⟨q, hq : 0 < q, m, _, rfl⟩
      rw [AlgHom.coe_toRingHom, lift_apply_dp]
      exact hJ.dpow_mem (ne_of_gt hq) (hf m)
    · rintro n a ⟨q, hq : 0 < q, m, _, rfl⟩
      rw [AlgHom.coe_toRingHom, lift_apply_dp, hJ.dpow_comp (ne_of_gt hq) (hf m), ← hh q m,
        h.dpow_comp (ne_of_gt hq) (ι_mem_augIdeal R M m), _root_.map_mul, map_natCast]
      apply congr_arg₂ _ rfl
      rw [hh, lift_apply_dp]

-- We open a namespace to privatize the complicated construction
namespace roby4
variable (A : Type u) [CommRing A]

/- The goal of this section is to establish [Roby1963, Lemme 4] (`condTFree_and_condD_to_condQ`),
  that under the above assumptions, `CondQ A` holds. It involves a lifting construction. -/

variable {S : Type u} [CommRing S] [Algebra A S] (I : Ideal S)
  (S₀ : Subalgebra A S) (hIS₀ : IsCompl (Subalgebra.toSubmodule S₀) (I.restrictScalars A))

-- We construct MvPolynomial S₀ A = A[S₀] →ₐ[A] S₀
instance : Algebra (MvPolynomial S₀ A) S₀ :=
  RingHom.toAlgebra (MvPolynomial.aeval id).toRingHom

theorem algebraMap_eq :
    algebraMap (MvPolynomial S₀ A) S₀ = (MvPolynomial.aeval id).toRingHom :=
  rfl -- RingHom.algebraMap_toAlgebra (algebraMap (MvPolynomial S₀ A) S₀)

--example : IsScalarTower A (MvPolynomial S₀ A) S₀ := inferInstance

/- instance : IsScalarTower A (MvPolynomial S A) S := {
  smul_assoc := fun a r s => by
    simp only [Algebra.smul_def, algebraMap_eq]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, _root_.map_mul, AlgHom.commutes]
    rw [← mul_assoc] } -/

/-- The linear map `(I →₀ A) →ₗ[A] S` sending `single i 1` to `i : S`. -/
def f : (I →₀ A) →ₗ[A] S := (Basis.constr (Finsupp.basisSingleOne) A) (fun i ↦ (i : S))

theorem f_mem_I (p) : f A I p ∈ I := by
  suffices LinearMap.range (f A I) ≤ Submodule.restrictScalars A I by
    apply this
    simp only [LinearMap.mem_range, exists_apply_eq_apply]
  simp only [f, Basis.constr_range, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, SetLike.coe_mem]

open Algebra Algebra.TensorProduct
section DecidableEq

variable [DecidableEq A] (hM : DividedPowers (augIdeal A (I →₀ A)))
  (hM_eq : ∀ n x, hM.dpow n ((ι A (I →₀ A)) x) = dp A n x)

instance hdpM_free : Module.Free A (DividedPowerAlgebra A (I →₀ A)) :=
  DividedPowerAlgebra.toModule_free _ _

instance hR_free : Module.Free A (MvPolynomial S A) :=
  Module.Free.of_basis (MvPolynomial.basisMonomials _ _)

/-- The divided power structure on the ideal `0` of `MvPolynomial S A`. -/
def hR [DecidableEq (MvPolynomial S A)] := dividedPowersBot (MvPolynomial S A)

theorem condτ [DecidableEq (MvPolynomial (↥S₀) A)] (condTFree : CondTFree A) :
    Condτ A (dividedPowersBot (MvPolynomial S₀ A)) hM := by apply condTFree

variable {I} (hI : DividedPowers I)

/-- The canonical extension of the map `f` to `DividedPowerAlgebra A (I →₀ A)`. -/
def Φ : DividedPowerAlgebra A (I →₀ A) →ₐ[A] S :=
  DividedPowerAlgebra.lift hI (f A I) (f_mem_I _ _)

/-- The map `Φ` as a DP morphism. -/
def dpΦ : DPMorphism hM hI := by
  apply DPMorphism.fromGens hM hI (augIdeal_eq_span _ _) (f := (Φ A hI).toRingHom)
  · rw [Ideal.map_le_iff_le_comap, augIdeal_eq_span, span_le]
    rintro x ⟨n, hn, b, _, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, SetLike.mem_coe, mem_comap, RingHom.coe_coe,
      Φ, lift_apply_dp]
    exact hI.dpow_mem (ne_of_gt hn) (f_mem_I A I b)
  · rintro n x ⟨m, hm, b, _, rfl⟩
    rw [Φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, lift_apply_dp, ← hM_eq,
      hM.dpow_comp (ne_of_gt hm) (ι_mem_augIdeal _ _ _),
      hI.dpow_comp (ne_of_gt hm) (f_mem_I A I b), _root_.map_mul, map_natCast]
    apply congr_arg₂ _ rfl
    rw [hM_eq, lift_apply_dp]

variable {A}

-- We consider `(MvPolynomial S₀ A) ⊗[A] DividedPowerAlgebra A (I →₀ A) →ₐ[A] S`
/-- The product of the algebra map `MvPolynomial S₀ A → S` and `Φ A hI`. -/
def Ψ : MvPolynomial S₀ A ⊗[A] DividedPowerAlgebra A (I →₀ A) →ₐ[A] S :=
  productMap ((Subalgebra.val S₀).comp (IsScalarTower.toAlgHom A (MvPolynomial S₀ A) S₀))
    (Φ A hI)

end DecidableEq

variable {A} {I} (hI : DividedPowers I)

theorem Ψ_eq (i) (hi : i ∈ I) :
    Ψ S₀ hI (includeRight (ι A _ (Finsupp.single ⟨i, hi⟩ 1 : I →₀ A))) = i := by
  simp [Ψ, Φ, f, Basis.constr_apply]

theorem Ψ_surjective (hIS₀ : IsCompl (Subalgebra.toSubmodule S₀) (I.restrictScalars A)) :
    Function.Surjective (Ψ S₀ hI) := by
  rw [← range_top_iff_surjective _, _root_.eq_top_iff]
  intro s _
  obtain ⟨s₀, hs₀, s₁, hs₁, rfl⟩ := Submodule.exists_add_eq_of_codisjoint (hIS₀.codisjoint) s
  apply Subalgebra.add_mem
  · -- case s₀ ∈ Subalgebra.toSubmodule S₀
    use (X ⟨s₀, hs₀⟩) ⊗ₜ[A] 1
    simp only [Ψ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productMap_apply_tmul, AlgHom.coe_comp,
      Subalgebra.coe_val, IsScalarTower.coe_toAlgHom', algebraMap_eq, Function.comp_apply, aeval_X,
      id_eq, map_one, mul_one]
  · -- case s₁ ∈ Submodule.restrictScalars A I
    use 1 ⊗ₜ[A] (ι A _ (Finsupp.single ⟨s₁, hs₁⟩ 1))
    simp only [Ψ, Φ, f, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, productMap_apply_tmul, map_one,
      lift_ι_apply, one_mul, Basis.constr_apply, Finsupp.basisSingleOne_repr,
      LinearEquiv.refl_apply, zero_smul, Finsupp.sum_single_index, one_smul]

theorem Ψ_map_eq : Subalgebra.map (Ψ S₀ hI)
    (Subalgebra.restrictScalars A (⊥ : Subalgebra (MvPolynomial S₀ A) _)) = S₀ := by
  ext x
  simp only [Subalgebra.mem_map, Subalgebra.mem_restrictScalars, Algebra.mem_bot, Set.mem_range,
    TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply, exists_exists_eq_and]
  constructor
  · rintro ⟨p, rfl⟩
    simp only [Ψ, productMap_apply_tmul, AlgHom.coe_comp, Subalgebra.coe_val,
      IsScalarTower.coe_toAlgHom', Function.comp_apply, map_one, mul_one, SetLike.coe_mem]
  · intro hx
    use MvPolynomial.X ⟨x, hx⟩
    simp only [Ψ, productMap_apply_tmul, AlgHom.coe_comp, Subalgebra.coe_val,
      IsScalarTower.coe_toAlgHom', Function.comp_apply, map_one, mul_one, algebraMap_eq,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, id_eq]

variable (I)

theorem K_eq_span [DecidableEq A] :
    K A (⊥ : Ideal (MvPolynomial S₀ A)) (augIdeal A (↥I →₀ A))
      = span (Set.image2 (fun n a ↦ 1 ⊗ₜ[A] dp A n a) {n | 0 < n} Set.univ) := by
  simp only [K, Ideal.map_bot, ge_iff_le, bot_le, sup_of_le_right, augIdeal_eq_span,
    Ideal.map_span, includeRight_apply, Set.image_image2]

variable {I}

/-- The divided power morphism from `(condτ A I S₀ hM condTFree).choose` to `hI`. -/
def dpΨ [DecidableEq A] [DecidableEq (MvPolynomial (↥S₀) A)]
    (hM : DividedPowers (augIdeal A (I →₀ A)))
    (hM_eq : ∀ n x, hM.dpow n ((ι A (I →₀ A)) x) = dp A n x) (condTFree : CondTFree A) :
    DPMorphism (condτ A I S₀ hM condTFree).choose hI := by
  apply DPMorphism.fromGens (condτ A I S₀ hM condTFree).choose hI
    (f := (Ψ S₀ hI).toRingHom) (K_eq_span I S₀)
  · -- Ideal.map (Ψ A S hI S₀).toRingHom (K A ⊥ (augIdeal A (↥I →₀ A))) ≤ I
    -- TODO: extract as equality in lemma
    simp only [AlgHom.toRingHom_eq_coe, K, Ideal.map_bot, ge_iff_le,
      bot_le, sup_of_le_right, map_le_iff_le_comap, augIdeal_eq_span, span_le]
    rintro _ ⟨n, hn, b, _, rfl⟩
    simp only [SetLike.mem_coe, mem_comap, Algebra.TensorProduct.includeRight_apply,
      RingHom.coe_coe, Ψ, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    exact (dpΦ A hM hM_eq hI).ideal_comp
      (Ideal.mem_map_of_mem _ (dp_mem_augIdeal A (I →₀ A) hn b))
  · rintro n _ ⟨m, hm, b, _, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    erw [← ((condτ A I S₀ hM condTFree).choose_spec.2).map_dpow (dp_mem_augIdeal _ _ hm _)]
    simp only [Ψ, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    erw [(dpΦ A hM hM_eq hI).dpow_comp _ (dp_mem_augIdeal _ _ hm _)]
    rfl

-- TODO: add to Mathlib (with _apply, as in Polynomial case)
/-- `MvPolynomial.C` as an `AlgHom`. -/
@[simps! apply]
def _root_.MvPolynomial.CAlgHom {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
     {σ : Type*} : A →ₐ[R] MvPolynomial σ A where
  toRingHom := C
  commutes' _ := rfl

-- NOTE: we are having the same issues with `map_zero` and `map_add` that we did with `map_smul`
-- (previously `AlgHom.map_smul`) in RobyLemma9.

lemma Subalgebra_tensorProduct_top_bot [Algebra A R]
    (S : Type*) [CommRing S] [Algebra A S] {S₀ : Subalgebra A S} (hS₀ : S₀ = ⊥)
    {T₀ : Subalgebra A R} (hT₀ : T₀ = ⊤) :
    Subalgebra.map (Algebra.TensorProduct.map T₀.val S₀.val) (⊤ : Subalgebra A (T₀ ⊗[A] S₀)) =
      Subalgebra.restrictScalars A (⊥ : Subalgebra R (R ⊗[A] S)) := by
  ext a
  simp only [Algebra.map_top, AlgHom.mem_range, Subalgebra.mem_restrictScalars, Algebra.mem_bot,
    Set.mem_range, Algebra.TensorProduct.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
  constructor
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero =>
        use 0
        simp only [TensorProduct.zero_tmul]
        exact (map_zero (Algebra.TensorProduct.map T₀.val S₀.val)).symm
        -- `rw [map_zero]` used to work, and it was much faster.
    | tmul a b =>
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp only [hS₀, Algebra.mem_bot, Set.mem_range] at hb
      obtain ⟨b, rfl⟩ := hb
      use b • a
      simp only [TensorProduct.smul_tmul, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val,
        Algebra.algebraMap_eq_smul_one]
    | add x y hx hy =>
      obtain ⟨rx, hx⟩ := hx
      obtain ⟨ry, hy⟩ := hy
      use rx + ry
      rw [TensorProduct.add_tmul, hx, hy]
      -- NOTE: The following `rw` times out. `rw [AlgHom.map_add]` used to work, but
      -- it is now deprecated.
      --rw [map_add (Algebra.TensorProduct.map T₀.val S₀.val) x y]
      exact Eq.symm (map_add (Algebra.TensorProduct.map T₀.val S₀.val) x y)
  · rintro ⟨r, rfl⟩
    exact ⟨⟨r, by rw [hT₀]; exact Algebra.mem_top⟩ ⊗ₜ[A] 1, rfl⟩

lemma map_psi_augIdeal_eq [DecidableEq A] (hM : DividedPowers (augIdeal A (I →₀ A)))
    (hM_eq : ∀ n x, hM.dpow n ((ι A (I →₀ A)) x) = dp A n x)
    (condTFree : CondTFree A) :
    Ideal.map (Ψ S₀ hI) (K A ⊥ (augIdeal A (I →₀ A))) = I := by
  classical
  apply le_antisymm (dpΨ S₀ hI hM hM_eq condTFree).ideal_comp
  intro i hi
  rw [← Ψ_eq S₀ hI i hi]
  exact mem_map_of_mem _ (mem_sup_right (mem_map_of_mem _ (ι_mem_augIdeal _ _ _)))

-- set_option trace.profiler true -- < 6 sec here!
-- Roby, lemma 4
theorem _root_.DividedPowerAlgebra.condTFree_and_condD_to_condQ [DecidableEq A]
    (condTFree: CondTFree A) (condD : CondD A) : CondQ A := by
  classical
  intro S _ _ I hI S₀ hIS₀
  let M := I →₀ A
  let R := MvPolynomial S₀ A
  let D := DividedPowerAlgebra A M
  obtain ⟨hM, hM_eq⟩ := condD M
  haveI hdpM_free : Module.Free A D := DividedPowerAlgebra.toModule_free A M
  haveI hR_free : Module.Free A R :=
    Module.Free.of_basis (MvPolynomial.basisMonomials _ _)
  -- We consider `R ⊗[A] DividedPowerAlgebra A M` as a comm ring and an A-algebra
  use R ⊗[A] D, by infer_instance, by infer_instance
  /- We need to add the fact that `R ⊗ DividedPowerAlgebra A M` is pregraduated in the sense of
    Roby, that is, the ideal is an augmentation ideal (given by tensor product).
    Note : in this case, it could maybe be given by base change, and it is not clear to me why
    this (simpler) approach does not suffice.
    In fact, `dpΨ` was proved above using that! -/
  have htop : Ideal.IsAugmentation (⊤ : Subalgebra A R) (⊥ : Ideal R) := by
    rw [isAugmentation_subalgebra_iff]
    exact isCompl_top_bot
  refine ⟨_, (condτ A I S₀ hM condTFree).choose, _,
    Ideal.isAugmentation_tensorProduct A htop (isAugmentation A M), ?_⟩
  use Ψ S₀ hI
  refine ⟨map_psi_augIdeal_eq S₀ hI hM hM_eq condTFree, ?_⟩
  constructor
  · -- Ψ maps the 0 part to S₀
    convert Ψ_map_eq S₀ hI using 2
    exact Subalgebra_tensorProduct_top_bot D (gradeZeroSubalgebra_eq_bot _ _) rfl
  exact ⟨Ψ_surjective S₀ hI (isAugmentation_subalgebra_iff.mp hIS₀),
    ⟨(dpΨ S₀ hI hM hM_eq condTFree).isDPMorphism, by infer_instance⟩⟩
  -- The `inferInstance` finds that the tensor product of free modules is free

-- The freeness of DividedPowerAlgebra of a free module still uses `sorry`
--#print axioms DividedPowerAlgebra.condTFree_and_condD_to_condQ

end roby4

lemma _root_.Ideal.map_toRingHom (A R S : Type*) [CommSemiring A] [Semiring R] [Algebra A R]
    [Semiring S] [Algebra A S] (f : R →ₐ[A] S) (I : Ideal R) :
    Ideal.map f I = Ideal.map f.toRingHom I := rfl


/- In Roby, all DP-algebras `A` considered are of the form `A₀ ⊕ A₊`, where `A₊` is the DP-ideal.
In other words, the DP-ideal is an augmentation ideal. Moreover, DP-morphisms map `A₀` to `B₀` and
`A₊` to `B₊`, so that their kernel is a direct sum `K₀ ⊕ K₊`.

Roby's framework is stated in terms of `pre-graded algebras`, namely graded algebras by the monoid
`{⊥, ⊤}` with carrier set `Fin 2` (with multiplication, `⊤ = 0` and `⊥ = 1`).

Most of the paper works in greater generality, as noted by Berthelot, but not all the results hold
in general. Berthelot gives an example (1.7) of a tensor product of algebras with divided power
ideals whose natural ideal does not have compatible divided powers.

[Berthelot, 1.7.1] gives the explicit property that holds for tensor products.
For an `A`-algebra `R` and `I : Ideal R`, one assumes the existence of `R₀ : Subalgebra A R` such
that `R = R₀ ⊕ I` as an `A`-module. Equivalently, the map `R →ₐ[A] R ⧸ I` has a left inverse.

In lemma 6, we have two surjective algebra morphisms `f : R →+* R'`,  `g : S →+* S'` and we consider
the induced surjective morphism `fg : R ⊗ S →+* R' ⊗ S'`.
`R` has a DP-ideal `I`,  `R'` has a DP-ideal `I'`, `S` has a DP-ideal `J`,  `S'` has a DP-ideal `J'`
with assumptions that `I' = map f I` and `J' = map g J`, with quotient DP structures.

Lemma 5 has proved that `fg.ker = (f.ker ⊗ 1) ⊔ (1 ⊗ g.ker)`.

The implicit hypothesis in lemma 6 is that `f` is homogeneous, i.e., maps `R₊ = I` to `R'₊ = J`
and `R₀` to `R'₀`, and same for `g`.

In the end, Roby applies his proposition 4 and makes use of yet another definition, namely of a
`divised ideal` : up to the homogeneous condition, this is exactly that `K ⊓ I` is a sub-pd-ideal.
The proof of proposition goes by using that `Ideal.span (s ∩ ↑I) = Ideal.span s ⊓ I` if `s`
consists of homogeneous elements.

So we assume the `roby` condition in the statement, in the hope that will be possible to prove it
each time we apply `condτ_rel`.
-/

/- While the following form is mathematically sufficient, it is probably simpler to prove lemma 6
as in Roby. The hypothsis will be that `RingHom.ker (Algebra.TensorProduct.map f g)` is generated
by a bunch of things that allow to prove that it is a “divised ideal” -/

-- Roby, abstracting lemma 6
example (A : Type u) [CommRing A] {R S R' S' : Type u} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra A R] [Algebra A S] [Algebra A R'] [Algebra A S']
    (f : R →ₐ[A] R') (hf : Function.Surjective f) {I : Ideal R} (hI : DividedPowers I)
    {I' : Ideal R'} (hI' : DividedPowers I') (hf' : IsDPMorphism hI hI' f) (hI'I : I' = I.map f)
    (g : S →ₐ[A] S') (hg : Function.Surjective g) {J : Ideal S} (hJ : DividedPowers J)
    {J' : Ideal S'} (hJ' : DividedPowers J') (hg' : IsDPMorphism hJ hJ' g) (hJ'J : J' = J.map g)
    (hRS : Condτ A hI hJ) : Condτ A hI' hJ' := by
  have roby : RingHom.ker (Algebra.TensorProduct.map f g) ⊓ K A I J =
        Ideal.map (Algebra.TensorProduct.includeLeft (S := A)) (RingHom.ker f ⊓ I)
          ⊔ Ideal.map (Algebra.TensorProduct.includeRight) (RingHom.ker g ⊓ J) := by
    sorry
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
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hK'_pd : IsSubDPIdeal hK (RingHom.ker fg ⊓ K A I J) := by
    rw [roby]
    exact IsSubDPIdeal_sup
      (IsSubDPIdeal_map_of_IsSubDPIdeal hK_pd.1 (IsSubDPIdeal_ker hI hI' hf'))
      (IsSubDPIdeal_map_of_IsSubDPIdeal hK_pd.2 (IsSubDPIdeal_ker hJ hJ' hg'))
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
      simp only [AlgHom.coe_toRingHom, Algebra.TensorProduct.includeLeft_apply]
      rw [← map_one g, ← Algebra.TensorProduct.map_tmul]
      rw [← AlgHom.coe_toRingHom f, hf'.2 a ha, RingHom.coe_coe]
      rw [← Algebra.TensorProduct.map_tmul]
      erw [Quotient.OfSurjective.dpow_apply hK s_fg hK'_pd]
      apply congr_arg
      exact hK_pd.1.2 a ha
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
      simp only [AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
      suffices ∀ y : S, fg.toRingHom (1 ⊗ₜ[A] y) = 1 ⊗ₜ[A] g y by
        rw [← this]
        rw [Quotient.OfSurjective.dpow_apply hK s_fg]
        have that := hg'.2 (n := n) a ha
        simp only [AlgHom.coe_toRingHom] at that ; rw [that]
        rw [← this]
        apply congr_arg
        simp only [← Algebra.TensorProduct.includeRight_apply]
        exact hK_pd.2.2 a ha
        apply Ideal.mem_sup_right
        apply Ideal.mem_map_of_mem _ ha
      intro x
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, map_one,
        fg]

theorem RingHom.ker_eq_span_union {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra A R]
    {R₀ : Subalgebra A R} {I : Ideal R}
    (hcI : Codisjoint (Subalgebra.toSubmodule R₀) (I.restrictScalars A)) {S : Type*} [CommRing S]
    [Algebra A S] {S₀ : Subalgebra A S} {J : Ideal S}
    (hdJ : Disjoint (Subalgebra.toSubmodule S₀) (J.restrictScalars A))
    (f : R →ₐ[A] S) (hf0 : f '' R₀ ≤ S₀) (hfI : f '' I ≤ J) :
    RingHom.ker f = Submodule.span _ (RingHom.ker f ∩ R₀ ∪ RingHom.ker f ∩ I) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.exists_add_eq_of_codisjoint hcI x
    simp [RingHom.mem_ker, map_add] at hx
    have hfy : f y = 0 := by
      rw [Submodule.disjoint_def] at hdJ
      apply hdJ (f y)
      · simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range, Subtype.exists] at hy ⊢
        exact hf0 (Set.mem_image_of_mem (⇑f) hy)
      · simp only [Submodule.restrictScalars_mem] at hz ⊢
        rw [add_eq_zero_iff_eq_neg] at hx
        rw [hx]
        apply neg_mem
        apply hfI
        exact ⟨z, hz, rfl⟩
    have hfz : f z = 0 := by rwa [hfy, zero_add] at hx
    rw [Submodule.span_union]
    apply Submodule.add_mem
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      simp only [Set.mem_inter_iff, SetLike.mem_coe, RingHom.mem_ker, hfy, true_and]
      simpa only [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range, Subtype.exists] using hy
    · apply Submodule.mem_sup_right
      apply Submodule.subset_span
      simp only [Submodule.restrictScalars_mem] at hz
      simp only [Set.mem_inter_iff, SetLike.mem_coe, RingHom.mem_ker, hfz, hz, and_self]
  · rw [Submodule.span_le]
    simp only [Set.union_subset_iff, Set.inter_subset_left, and_self]

example (A : Type u) [CommRing A]
    {R : Type u} [CommRing R] [Algebra A R]
    {R₀ : Subalgebra A R} {I : Ideal R} (hR₀I : I.IsAugmentation R₀) (hI : DividedPowers I) :
    Codisjoint (Subalgebra.toSubmodule R₀) (I.restrictScalars A) := by
  have := hR₀I.codisjoint
  sorry

theorem RingHom.ker_eq_span_union' (A : Type*) [CommRing A]
    (R : Type*) [CommRing R] [Algebra A R]
    (R₀ : Subalgebra A R) (I : Ideal R) (hI : I.IsAugmentation R₀)
    (S : Type*) [CommRing S] [Algebra A S]
    (S₀ : Subalgebra A S) (J : Ideal S) (hJ : J.IsAugmentation S₀)
    (f : R →ₐ[A] S) (hf0 : f '' R₀ ≤ S₀) (hfI : f '' I ≤ J) :
    RingHom.ker f ⊓ I = Submodule.span _ (RingHom.ker f ∩ I) := by
  apply le_antisymm
  · rw [RingHom.ker_eq_span_union ?_  ?_ f hf0 hfI]
    sorry
    · convert hI.codisjoint
      sorry
    · convert hJ.disjoint
      sorry
  · sorry

/-- Roby, Lemma 6, the condition τ descends by quotient -/
theorem condτ_rel (A : Type u) [CommRing A]
    {R : Type u} [CommRing R] [Algebra A R]
    {R₀ : Subalgebra A R} {I : Ideal R} (hR₀I : I.IsAugmentation R₀) (hI : DividedPowers I)
    {S : Type u} [CommRing S] [Algebra A S]
    {S₀ : Subalgebra A S} {J : Ideal S} (hS₀J : J.IsAugmentation S₀) (hJ : DividedPowers J)
    {R' : Type u} [CommRing R'] [Algebra A R']
    {R₀' : Subalgebra A R'} {I' : Ideal R'} (hR₀I' : I'.IsAugmentation R₀') (hI' : DividedPowers I')
    {S' : Type u} [CommRing S'] [Algebra A S']
    {S₀' : Subalgebra A S'} {J' : Ideal S'} (hS₀J' : J'.IsAugmentation S₀') (hJ' : DividedPowers J')
    (f : R →ₐ[A] R') (hf : Function.Surjective f) (hfDP : IsDPMorphism hI hI' f)
    (hfR₀ : R₀' = Subalgebra.map f R₀) (hI'I : I' = I.map f)
    (g : S →ₐ[A] S') (hg : Function.Surjective g) (hgDP : IsDPMorphism hJ hJ' g)
    (hgS₀ : S₀' = Subalgebra.map g S₀) (hJ'J : J' = J.map g)
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
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hK'_pd : IsSubDPIdeal hK (RingHom.ker fg ⊓ K A I J) := by
    have := Algebra.TensorProduct.map_ker _ _ hf hg
    have hkerf := RingHom.ker_eq_span_union (isAugmentation_subalgebra_iff.mp hR₀I).codisjoint
      (isAugmentation_subalgebra_iff.mp hR₀I').disjoint f
      (by simp only [hfR₀, Subalgebra.coe_map, le_refl])
      (by simp only [hI'I, Ideal.map, Set.le_eq_subset]; apply Submodule.subset_span)
    have hkerg := RingHom.ker_eq_span_union (isAugmentation_subalgebra_iff.mp hS₀J).codisjoint
      (isAugmentation_subalgebra_iff.mp hS₀J').disjoint g
      (by simp only [hgS₀, Subalgebra.coe_map, le_refl])
      (by simp only [hJ'J, Ideal.map, Set.le_eq_subset]; apply Submodule.subset_span)
    rw [hkerf, hkerg] at this
    simp only [submodule_span_eq, Ideal.span_union, Ideal.map_sup] at this
    rw [sup_sup_sup_comm] at this
    simp only [Ideal.map_span] at this
    rw [this]
    -- we need a variant of `IsSubDPIdeal_sup`
    suffices this :
      ((span (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := R) (B := S) ''
        (↑(RingHom.ker f) ∩ (R₀ : Set R))) ⊔
            span (⇑Algebra.TensorProduct.includeRight '' (↑(RingHom.ker g) ∩ ↑S₀)) ⊔
          (span (⇑Algebra.TensorProduct.includeLeft '' (↑(RingHom.ker f) ∩ ↑I)) ⊔
            span (⇑Algebra.TensorProduct.includeRight '' (↑(RingHom.ker g) ∩ ↑J)))) ⊓
        K A I J) = ((span (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := R) (B := S) ''
          (↑(RingHom.ker f) ∩ ↑I)) ⊔
        span (⇑Algebra.TensorProduct.includeRight '' (↑(RingHom.ker g) ∩ ↑J)))) by
      rw [this]
      simp only [← Ideal.map_span]
      apply IsSubDPIdeal_sup
      · have : span (↑(RingHom.ker f) ∩ ↑I) = RingHom.ker f ⊓ I := sorry
        rw [this]
        exact IsSubDPIdeal_map_of_IsSubDPIdeal hK_pd.1 (IsSubDPIdeal_ker hI hI' hfDP)
      · have : span (↑(RingHom.ker g) ∩ ↑J) = RingHom.ker g ⊓ J := sorry
        rw [this]
        exact IsSubDPIdeal_map_of_IsSubDPIdeal hK_pd.2 (IsSubDPIdeal_ker hJ hJ' hgDP)
    sorry
  rw [hK_map]
  use DividedPowers.Quotient.OfSurjective.dividedPowers hK s_fg hK'_pd
  constructor
  · -- hI'.is_pd_morphism hK' ↑(i_1 A R' S')
    constructor
    · rw [← hK_map, Ideal.map_le_iff_le_comap]
      exact fun _ ha' ↦ Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha')
    · intro n a' ha'
      simp only [hI'I, Ideal.mem_map_iff_of_surjective f hf] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      simp only [AlgHom.coe_toRingHom, Algebra.TensorProduct.includeLeft_apply]
      rw [← map_one g, ← Algebra.TensorProduct.map_tmul, ← AlgHom.coe_toRingHom f, hfDP.2 a ha,
        RingHom.coe_coe, ← Algebra.TensorProduct.map_tmul]
      erw [Quotient.OfSurjective.dpow_apply hK s_fg hK'_pd (mem_sup_left (mem_map_of_mem _ ha))]
      exact congr_arg _ (hK_pd.1.2 a ha)
  · -- hJ'.is_pd_morphism hK' ↑(i_2 A R' S')
    constructor
    · rw [← hK_map, map_le_iff_le_comap]
      exact fun _ ha' ↦ mem_sup_right (Ideal.mem_map_of_mem _ ha')
    · intro n a' ha'
      simp only [hJ'J, Ideal.mem_map_iff_of_surjective g hg] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      simp only [AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
      suffices ∀ y : S, fg.toRingHom (1 ⊗ₜ[A] y) = 1 ⊗ₜ[A] g y by
        rw [← this, Quotient.OfSurjective.dpow_apply hK s_fg]
        · have that := hgDP.2 (n := n) a ha
          simp only [AlgHom.coe_toRingHom] at that;
          rw [that, ← this]
          exact congr_arg _ (hK_pd.2.2 a ha)
        exact mem_sup_right (mem_map_of_mem _ ha)
      intro x
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        map_one, fg]

open Submodule

-- Roby, Variante de la proposition 4
theorem roby_prop_4' {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra A R] {I : Ideal R}
    {R₀ : Subalgebra A R} (hsplit : IsAugmentation R₀ I) {J : Ideal R} {F₀ : Set R₀} {FI : Set I}
    (hJ : J = span R ((R₀.val '' F₀) ∪ (I.subtype '' FI) : Set R)) :
    J.restrictScalars R₀ = (Subalgebra.toSubmodule ⊥ ⊓ J.restrictScalars R₀)
      ⊔ (I.restrictScalars R₀ ⊓ J.restrictScalars R₀) := by
  rcases hsplit with ⟨hd, hc⟩
  simp only [disjoint_def, Subalgebra.mem_toSubmodule, restrictScalars_mem] at hd
  refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  intro x hx
  simp only [hJ, SetLike.coe_sort_coe, restrictScalars_mem] at hx
  apply span_induction hx (p := fun x ↦ x ∈ _) _ (zero_mem _) (fun x y hx hy ↦ add_mem hx hy)
  · intro a x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.exists_add_eq_of_codisjoint hc a
    simp only [Submodule.mem_sup, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
      restrictScalars_mem] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range, Subtype.exists] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    rw [add_smul]
    refine add_mem ?_ (Submodule.mem_sup_right
        ⟨mul_mem_right (y + z) I hb, mul_mem_left J b (add_mem hy.right hz.right)⟩)
    apply smul_mem _ _ (add_mem (Submodule.mem_sup_left _) (Submodule.mem_sup_right _)) <;>
    simp only [Submodule.mem_inf, Subalgebra.mem_toSubmodule, hy, Submodule.restrictScalars_mem,
        and_self, hz]
  · rintro _ (⟨⟨x, hx'⟩, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · apply Submodule.mem_sup_left
      simp only [Submodule.mem_inf, Subalgebra.mem_toSubmodule, restrictScalars_mem]
      refine ⟨⟨⟨x, hx'⟩, rfl⟩, ?_⟩
      · rw [hJ]
        apply Submodule.subset_span (Set.mem_union_left _ _)
        simp only [Subalgebra.coe_val, Set.mem_image, Subtype.exists, exists_and_right,
          exists_eq_right, hx, hx', exists_const]
    · apply Submodule.mem_sup_right
      simp only [hJ, SetLike.coe_sort_coe, submodule_span_eq, Submodule.mem_inf,
        restrictScalars_mem, SetLike.coe_mem, true_and]
      refine ⟨by simp only [Submodule.coe_subtype, SetLike.coe_mem], ?_⟩
      · apply Submodule.subset_span (Set.mem_union_right _ _)
        simp only [Submodule.coe_subtype, Set.mem_image, SetLike.coe_eq_coe, exists_eq_right, hy]

-- Roby, Variante de la proposition 4
theorem roby_prop_4'' {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra A R] {I : Ideal R}
    {R₀ : Subalgebra A R} (hsplit : IsAugmentation R₀ I) {J : Ideal R} {F₀ : Set R₀} {FI : Set I}
    (hJ : J = Submodule.span R ((R₀.val '' F₀) ∪ (I.subtype '' FI) : Set R)) :
    J ⊓ I = span (I.subtype '' FI) := by
  rcases hsplit with ⟨hd, hc⟩
  apply le_antisymm
  · intro x
    simp only [Ideal.mem_inf, SetLike.coe_sort_coe, and_imp]
    intro hx hx'
    rw [hJ] at hx
    sorry
  · simp only [Ideal.span_le, SetLike.coe_sort_coe, Submodule.inf_coe,
      Set.subset_inter_iff]
    exact ⟨hJ ▸ subset_trans Set.subset_union_right Ideal.subset_span, Subtype.coe_image_subset _ _⟩


/-
  simp only [Submodule.disjoint_def, Subalgebra.mem_toSubmodule,
    Submodule.restrictScalars_mem] at hd
  refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  intro x hx
  simp only [hJ, SetLike.coe_sort_coe, Submodule.restrictScalars_mem] at hx
  apply Submodule.span_induction hx (p := fun x ↦ x ∈ _)
  · rintro _ (⟨⟨x, hx'⟩, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · apply Submodule.mem_sup_left
      simp only [Submodule.mem_inf, Subalgebra.mem_toSubmodule, Submodule.restrictScalars_mem]
      constructor
      · rw [Algebra.mem_bot]
        exact ⟨⟨x, hx'⟩, rfl⟩
      rw [hJ]
      apply Submodule.subset_span
      apply Set.mem_union_left
      simp only [SetLike.coe_sort_coe, Set.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, hx, exists_prop, and_true, hx']
    · apply Submodule.mem_sup_right
      simp only [hJ, SetLike.coe_sort_coe, submodule_span_eq, Submodule.mem_inf,
        Submodule.restrictScalars_mem, SetLike.coe_mem, true_and]
      apply Submodule.subset_span
      apply Set.mem_union_right
      simp only [Set.mem_image, SetLike.coe_eq_coe, exists_eq_right, hy]
  · exact zero_mem _
  · exact fun x y hx hy ↦ add_mem hx hy
  · intro a x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.exists_add_eq_of_codisjoint hc a
    simp only [Submodule.mem_sup, Submodule.mem_inf, Subalgebra.mem_toSubmodule, Submodule.restrictScalars_mem] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    simp only [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range, Subtype.exists] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    simp only [Submodule.restrictScalars_mem] at hb
    rw [add_smul]
    apply add_mem
    · apply Submodule.smul_mem
      apply add_mem
      · apply Submodule.mem_sup_left
        simp only [Submodule.mem_inf, Subalgebra.mem_toSubmodule, hy, Submodule.restrictScalars_mem,
          and_self]
      · apply Submodule.mem_sup_right
        simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, hz, and_self]
    · apply Submodule.mem_sup_right
      exact ⟨mul_mem_right (y + z) I hb, mul_mem_left J b (add_mem hy.right hz.right)⟩
-/

theorem ne_zero_of_mem_antidiagonal_ne_zero {M : Type*} [AddCommMonoid M] [HasAntidiagonal M]
    {x : M × M} {m : M} (hx : x ∈ antidiagonal m) (hm : m ≠ 0) :
    x.1 ≠ 0 ∨ x.2 ≠ 0 := by
  rw [← not_and_or]
  intro h
  apply hm
  simpa only [mem_antidiagonal, h.1, h.2, eq_comm, add_zero] using hx

-- I don't think this is needed.
/- theorem Submodule.restrictScalars_sup {A R M : Type*} [CommSemiring A] [Semiring R] [Algebra A R]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower A R M] {U V : Submodule R M} :
    Submodule.restrictScalars A (U ⊔ V) =
      Submodule.restrictScalars A U ⊔ Submodule.restrictScalars A V :=
  Submodule.sup_restrictScalars A U V -/

-- Roby, Proposition 4
theorem roby_prop_4 {A : Type*} [CommRing A] {R : Type*} [CommRing R] [Algebra A R] {I : Ideal R}
    {R₀ : Subalgebra A R} (hsplit : IsAugmentation R₀ I) (hI : DividedPowers I) {J : Ideal R}
    {F₀ : Set R₀} {FI : Set I}
    (hJ : J = Submodule.span R ((R₀.val '' F₀) ∪ (I.subtype '' FI) : Set R)) :
    hI.IsSubDPIdeal (J ⊓ I) ↔ (∀ a ∈ FI, ∀ n ≠ 0, hI.dpow n a ∈ J):= by
  simp only [Ideal.isAugmentation_subalgebra_iff] at hsplit
  constructor
  · intro hJ' a ha n hn
    apply inf_le_right (a := J)
    simp only [ge_iff_le, le_refl, inf_of_le_left]
    apply inf_le_left (b := I)
    apply hJ'.dpow_mem hn
    simp only [Ideal.mem_inf, SetLike.coe_mem, and_true]
    exact hJ ▸ Ideal.subset_span (Set.mem_union_right _ ⟨a, ha, rfl⟩)
  · intro H
    set T := { s ∈ J ⊓ I | ∀ n ≠ 0, hI.dpow n s ∈ J } with hT
    -- We prove that T is a subideal of J ⊓ I
    have hT_le : span T ≤ J ⊓ I := Ideal.span_le.mpr (fun t ht ↦ Set.mem_of_mem_inter_left ht)
    have hT' : T = span T := by
      ext t
      refine ⟨fun ht ↦ Ideal.subset_span ht, ?_⟩
      intro (ht : t ∈ span T)
      simp only [hT, Set.mem_setOf_eq]
      refine ⟨hT_le ht, ?_⟩
      induction ht using Submodule.span_induction' with
      | mem t ht => exact fun n hn ↦ ht.2 n hn
      | zero => exact fun n hn ↦ by simp only [hI.dpow_eval_zero hn, zero_mem]
      | add a ha b hb ha' hb' =>
        intro n hn
        rw [hI.dpow_add (inf_le_right (a := J) (hT_le ha)) (inf_le_right (a := J) (hT_le hb))]
        apply Ideal.sum_mem
        rintro ⟨u, v⟩ h
        rcases ne_zero_of_mem_antidiagonal_ne_zero h hn with (hu | hv)
        · exact J.mul_mem_right _ (ha' u hu)
        · exact J.mul_mem_left _ (hb' v hv)
      | smul a x hx hx' =>
        intro n hn
        rw [smul_eq_mul, hI.dpow_smul (inf_le_right (a := J) (hT_le hx))]
        exact Ideal.mul_mem_left _ _ (hx' n hn)
    suffices T = J ⊓ I by exact {
      isSubideal := inf_le_right
      dpow_mem := fun hn a ha ↦ by
        simp only [Ideal.mem_inf] at ha ⊢
        suffices ha' : a ∈ T by
          exact ⟨ha'.2 _ hn, hI.dpow_mem hn ha.2⟩
        simp only [this, Submodule.inf_coe, Set.mem_inter_iff, SetLike.mem_coe, ha.2, ha.1, and_true] }
    set U := (J.restrictScalars A ⊓ Subalgebra.toSubmodule R₀) ⊔
      (Ideal.span T).restrictScalars A with hU
    suffices U = J.restrictScalars A by
      rw [hT']
      ext t
      simp only [SetLike.mem_coe]
      refine ⟨fun ht ↦ hT_le ht, ?_⟩
      simp only [Ideal.mem_inf]
      rintro ⟨ht, ht'⟩
      rw [← Submodule.restrictScalars_mem A, ← this, Submodule.mem_sup] at ht
      obtain ⟨y, hy, z, hz, rfl⟩ := ht
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem,
        Subalgebra.mem_toSubmodule] at hy hz
      apply Submodule.add_mem _ _ hz
      suffices y = 0 by
        simp only [this, zero_mem]
      have hz' := Ideal.mem_inf.mp (hT_le hz)
      apply Submodule.disjoint_def.mp hsplit.disjoint
      simp only [Subalgebra.mem_toSubmodule, hy.2, Submodule.restrictScalars_mem]
      exact add_sub_cancel_right y z ▸ Submodule.sub_mem _ ht' hz'.2
    suffices Submodule.span R U = J by
      ext u
      simp only [← this, Submodule.restrictScalars_mem]
      refine ⟨fun hu ↦ Submodule.subset_span hu, fun hu ↦ ?_⟩
      induction hu using Submodule.span_induction' with
      | mem _ hu => exact hu
      | zero => exact zero_mem U
      | add x _ y _ hx' hy' => exact U.add_mem hx' hy'
      | smul a x hx hx' =>
        obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.exists_add_eq_of_codisjoint hsplit.codisjoint a
        simp only [Subalgebra.mem_toSubmodule, Submodule.restrictScalars_mem] at hb hc
        rw [add_smul, smul_eq_mul]
        simp only [hU, Submodule.mem_sup, Submodule.mem_inf,
            Submodule.restrictScalars_mem, Subalgebra.mem_toSubmodule] at hx'
        obtain ⟨y, ⟨hy, hy'⟩, z, hz, rfl⟩ := hx'
        apply Submodule.add_mem
        · simp only [mul_add]
          exact Submodule.add_mem _
            (Submodule.mem_sup_left ⟨J.mul_mem_left b hy, R₀.mul_mem hb hy'⟩)
            (Submodule.mem_sup_right (Ideal.mul_mem_left _ b hz))
        · apply Submodule.mem_sup_right
          simp only [smul_eq_mul, Submodule.restrictScalars_mem, mul_add]
          apply Submodule.add_mem _ _ (Ideal.mul_mem_left _ _ hz)
          suffices c * y ∈ T by rwa [hT', SetLike.mem_coe] at this
          simp only [hT, Ideal.mem_inf, Set.mem_setOf_eq]
          refine ⟨⟨Ideal.mul_mem_left _ _ hy, Ideal.mul_mem_right _ _ hc⟩, fun _ hn ↦ ?_⟩
          rw [hI.dpow_mul_right hc]
          apply Ideal.mul_mem_left
          rw [← Nat.succ_pred_eq_of_ne_zero hn, pow_succ]
          exact Ideal.mul_mem_left _ _ hy
    apply le_antisymm
    · rw [Submodule.span_le, hU]
      intro j hj
      simp only [SetLike.mem_coe, Submodule.mem_sup, Submodule.mem_inf,
        Submodule.restrictScalars_mem, Subalgebra.mem_toSubmodule] at hj
      obtain ⟨y, ⟨hy, _⟩, z, hz, rfl⟩ := hj
      exact Submodule.add_mem _ hy (inf_le_left (b := I) (hT_le hz))
    · simp only [hJ, SetLike.coe_sort_coe, Ideal.span_union, submodule_span_eq, sup_le_iff]
      constructor
      · rw [Ideal.span_le]
        rintro a ⟨⟨b, hb⟩, hb', rfl⟩
        apply Ideal.subset_span (Submodule.mem_sup_left _)
        simp only [Submodule.mem_inf, restrictScalars_mem, Subalgebra.mem_toSubmodule, hb, and_true]
        rw [hJ]
        exact ⟨Ideal.subset_span (Set.mem_union_left _ ⟨⟨b, hb⟩, hb', rfl⟩) , hb⟩
      · rw [Ideal.span_le]
        rintro a ⟨⟨b, hb⟩, hb', rfl⟩
        apply Ideal.subset_span (Submodule.mem_sup_right _)
        simp only [restrictScalars_mem]
        suffices b ∈ T by rwa [hT'] at this
        simp only [hT, Set.mem_setOf_eq]
        exact ⟨Ideal.mem_inf.mpr ⟨hJ ▸ Ideal.subset_span
          (Set.mem_union_right _ ⟨⟨b, hb⟩, hb', rfl⟩), hb⟩, fun n hn ↦ H _ hb' n hn⟩

-- Unused
/- theorem Ideal.map_coe_toRingHom
  {A : Type*} [CommRing A] {R S : Type*} [CommRing R] [CommRing S]
  [Algebra A R] [Algebra A S] (f : R →ₐ[A] S)
  (I : Ideal R) : Ideal.map f I = Ideal.map f.toRingHom I := by
  rfl -/

example (A : Type*) [CommRing A]
    (R : Type*) [CommRing R] [Algebra A R]
    (R₀ : Subalgebra A R) (I : Ideal R) (_ : Ideal.IsAugmentation R₀ I)
    (S : Type*) [CommRing S] [Algebra A S]
    (S₀ : Subalgebra A S) (J : Ideal S) (_ : Ideal.IsAugmentation S₀ J) :
    let T₀ : Subalgebra A (R ⊗[A] S) :=
      Subalgebra.map
        (Algebra.TensorProduct.map R₀.val S₀.val : R₀ ⊗[A] S₀ →ₐ[A] R ⊗[A] S)
        (⊤ : Subalgebra A (R₀ ⊗[A] S₀))
    Ideal.IsAugmentation (T₀) (K A I J) := sorry

-- Roby, lemma 7
theorem CondQ_and_condTFree_imply_condT (A : Type*) [CommRing A] (hQ : CondQ A)
    (hT_free : CondTFree A) : CondT A := by
  intro R' _ _ I' hI' R₀' hIR₀' S' _ _ J' hJ' S₀' hJS₀'
  obtain ⟨R, _, _, I, hI, R₀, hIR₀, f, hfI, hfR₀, hf, hfDP, hR_free⟩ := hQ R' I' hI' R₀' hIR₀'
  obtain ⟨S, _, _, J, hJ, S₀, hJS₀, g, hgJ, hgS₀, hg, hgDP, hS_free⟩ := hQ S' J' hJ' S₀' hJS₀'
  exact condτ_rel A hIR₀ hI hJS₀ hJ hIR₀' hI' hJS₀' hJ' f hf hfDP hfR₀.symm hfI.symm g hg hgDP
    hgS₀.symm hgJ.symm (hT_free R _ _ _)

-- Roby, lemma 8
-- TODO: remove (the proof in Roby 65 is incorrect)
theorem condT_and_condD_imply_condD (A : Type u) [CommRing A] [DecidableEq A]
    (condT : CondT A) (condD : CondD A)
    (R : Type v) [CommRing R] [DecidableEq R] [Algebra A R] :
    CondD R := by
  sorry
  -- Commented out because we changed R from Type u to Type v
  /- classical
  intro M _ _
  letI : Module A M := Module.compHom M (algebraMap A R)
  letI : IsScalarTower A R M :=
    IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
  set D := R ⊗[A] DividedPowerAlgebra A M
  obtain ⟨hM, hM_eq⟩ := condD M
  have hMa := isAugmentation A M
  set hR : DividedPowers (⊥ : Ideal R) := dividedPowersBot R
  have hRa : IsAugmentation (⊤ : Subalgebra A R) (⊥ : Ideal R) := by
    rw [isAugmentation_subalgebra_iff A]
    exact IsCompl.symm { disjoint := fun ⦃x⦄ a a_1 ↦ a, codisjoint := fun ⦃x⦄ a a ↦ a }
  obtain ⟨hD, hhD1, hhD2⟩ := condT R hR hRa (DividedPowerAlgebra A M) hM hMa -/

/- Note (2024-07-12) — Roby claims that there is an “obvious” isomorphism
`e : D ≃ₐ[R] DividedPowerAlgebra R M` that maps the ideal `K` to the augmentation ideal
`augIdeal R M`. Using this isomorphism, the divided powers `hD` on `D` would
be transfered to `DividedPowerAlgebra R M` to give the desired divided power structure.
Unfortunately, [Roby, 1963, III.3] `dpScalarExtensionEquiv` proves something else, namely
`D ≃ₐ[R] DividedPowerAlgebra R (R ⊗[A] M)`
I don't know how this can be repaired…

Note (2024-07-15) — When `R = ℤ`, Roby's construction of divided powers on the augmentation ideal
of `DividedPowerAlgebra R M` splits into two cases:
- he first considers the case where `M` is free.
- then he writes `M` as a quotient of a free `R`-module `L` and invokes
  his earlier paper for a description of the kernel of the natural morphism
    `DividedPowerAlgebra R L →ₐ[R] DividedPowerAlgebra R M`.
  It seems that this approach could work in general. I hope so…

  -/

-- Roby, lemma 9 is in `RobyLemma9.lean`.

-- Roby, lemma 10
theorem condT_implies_condTFree (A : Type*) [CommRing A] (R : Type*) [CommRing R] [Algebra A R]
    (hA : CondT A) : CondTFree R :=
  sorry

-- Roby, lemma 11
theorem condTFree_int : CondTFree ℤ :=
  sorry

-- Roby, lemma 12
theorem condD_int : CondD ℤ :=
  sorry

theorem CondQ_int : CondQ ℤ :=
  condTFree_and_condD_to_condQ condTFree_int condD_int

theorem condT_int : CondT ℤ :=
  CondQ_and_condTFree_imply_condT ℤ CondQ_int condTFree_int

-- We need an alternative proof
theorem condD_holds (A : Type*) [CommRing A] [DecidableEq A] : CondD A :=
  sorry --condT_and_condD_imply_condD ℤ condT_int condD_int A

theorem condTFree_holds (A : Type*) [CommRing A] : CondTFree A :=
  condT_implies_condTFree ℤ A condT_int

theorem CondQ_holds (A : Type*) [CommRing A] [DecidableEq A] : CondQ A :=
  condTFree_and_condD_to_condQ (condTFree_holds A) (condD_holds A)

theorem condT_holds (A : Type*) [CommRing A] [DecidableEq A] : CondT A :=
  CondQ_and_condTFree_imply_condT A (CondQ_holds A) (condTFree_holds A)

end Roby_section9

-- Formalization of Roby65, section 10
section Roby_section10

open DividedPowers DividedPowerAlgebra

-- namespace divided_power_algebra
-- Part of Roby65 Thm 1
/-- The divided power structure on the augmentation ideal. -/
def dividedPowers' (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M]
    [Module A M] : DividedPowers (augIdeal A M) :=
  (condD_holds A M).choose

theorem dpow_ι (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M] [Module A M]
    (x : M) (n : ℕ) : dpow (dividedPowers' A M) n (ι A M x) = dp A n x :=
  (condD_holds A M).choose_spec n x

theorem dp_comp (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M] [Module A M]
    (x : M) {n : ℕ} (m : ℕ) (hn : n ≠ 0) :
    dpow (dividedPowers' A M) m (dp A n x) = ↑(Nat.uniformBell m n) * dp A (m * n) x := by
  erw [← (condD_holds A M).choose_spec, dpow_comp _ hn (ι_mem_augIdeal A M x), dpow_ι]

theorem roby_theorem_2 (R : Type u) [CommRing R]  [DecidableEq R] (M : Type u) [AddCommGroup M]
    [Module R M] {A : Type u} [CommRing A] [Algebra R A] {I : Ideal A} (hI : DividedPowers I)
    {φ : M →ₗ[R] A} (hφ : ∀ m, φ m ∈ I) :
    IsDPMorphism (dividedPowers' R M) hI (DividedPowerAlgebra.lift hI φ hφ) :=
  cond_D_uniqueness _ (fun _ _ ↦  dpow_ι _ _ _ _) _ _ _

lemma ι_comp_mem_augIdeal (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Type w) [CommRing S] [DecidableEq S] [Algebra R S] {N : Type w} [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) (m : M) :
    ((ι S N).restrictScalars R).comp f m ∈ augIdeal S N := by
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, ι_mem_augIdeal S N (f m)]

theorem lift_eq_DPLift (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Type w) [CommRing S] [DecidableEq S] [Algebra R S] {N : Type w} [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) :
    LinearMap.lift S f = DividedPowerAlgebra.lift (dividedPowers' S N)
      (((ι S N).restrictScalars R).comp f) (ι_comp_mem_augIdeal R S f) := by
  refine DividedPowerAlgebra.algHom_ext (fun _ _ ↦ ?_)
  simp only [lift_apply_dp, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    DividedPowerAlgebra.LinearMap.lift_apply_dp, ι, LinearMap.coe_mk, AddHom.coe_mk,
    dp_comp _ _ _ _ Nat.one_ne_zero, uniformBell_one', Nat.cast_one, mul_one, one_mul]

theorem roby_prop_8 (R : Type u) [DecidableEq R] [CommRing R] {M : Type u} [AddCommGroup M]
    [Module R M] (S : Type u) [DecidableEq S] [CommRing S] [Algebra R S] {N : Type u}
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) :
    IsDPMorphism (dividedPowers' R M) (dividedPowers' S N) (LinearMap.lift S f) :=
  lift_eq_DPLift R S f ▸ roby_theorem_2 R M (dividedPowers' S N) (ι_comp_mem_augIdeal R S f)

end Roby_section10

end DividedPowerAlgebra
