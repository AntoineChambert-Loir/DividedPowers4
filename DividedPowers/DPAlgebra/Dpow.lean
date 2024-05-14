import DividedPowers.DPAlgebra.Init
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.RatAlgebra
import DividedPowers.SubDPIdeal
import DividedPowers.IdealAdd
import DividedPowers.DPAlgebra.RobyLemma9
import DividedPowers.DPAlgebra.PolynomialMap
import DividedPowers.ForMathlib.RingTheory.Ideal
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Construction of divided powers of tensor products of divided power algebras

The two main constructions of this file are the following:

* Let `R`, `A`, `B` be commutative rings, with `Algebra R A` and `Algebra R B`.
Assume that `A` and `B` have divided power structures.
We construct the unique divided power structure on `A ⊗[R] B` so that
the canonical morphisms `A →ₐ[R] A ⊗[R] B` and `B →ₐ[R] A ⊗[R] B`
are dp-morphisms.

* Let `R` be a commutative ring, `M` an `R`-module.
We construct the unique divided power structure on `DividedPowerAlgebra R M`
for which `dpow n (DividedPower.linearEquivDegreeOne m) = dp n m` for any `m : M`,
where `linearEquivDegreeOne` is the `LinearEquiv`  from `M`
to the degree 1 part of `DividedPowerAlgebra R M`

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
paper [Roby1965]. This formalization would be the second one.

-/
noncomputable section

universe u v v₁ v₂ w

section

variable (R M : Type u) [CommRing R] [DecidableEq R] [AddCommGroup M] [DecidableEq M]
  [Module R M]

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

def Condδ (R : Type u) [CommRing R] [DecidableEq R] (M : Type u) [AddCommGroup M] [Module R M] :
    Prop :=
  ∃ h : DividedPowers (augIdeal R M), ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x
#align divided_power_algebra.cond_δ DividedPowerAlgebra.Condδ

set_option linter.uppercaseLean3 false
def CondD (R : Type u) [CommRing R] [DecidableEq R] : Prop :=
  ∀ (M : Type u) [AddCommGroup M], ∀ [Module R M], Condδ R M
#align divided_power_algebra.cond_D DividedPowerAlgebra.CondD

end DividedPowerAlgebra

end

section Roby

-- Formalization of Roby 1965, section 8
open Finset MvPolynomial Ideal.Quotient

-- triv_sq_zero_ext
open Ideal

-- direct_sum
open RingQuot

open DividedPowers

namespace DividedPowerAlgebra

open DividedPowerAlgebra

section TensorProduct

open scoped TensorProduct

variable (A R S : Type u) [CommRing A] [CommRing R] [Algebra A R] [CommRing S] [Algebra A S]
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
    (hJK : isDPMorphism hJ hK (i2 A R S)) (hJK' : isDPMorphism hJ hK' (i2 A R S)) : hK = hK' := by
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

def Condτ (A : Type u) [CommRing A] {R : Type u} [CommRing R] [Algebra A R] {S : Type u}
    [CommRing S] [Algebra A S] {I : Ideal R} {J : Ideal S} (hI : DividedPowers I)
    (hJ : DividedPowers J) : Prop :=
  ∃ hK : DividedPowers (K A I J), isDPMorphism hI hK (i1 A R S) ∧ isDPMorphism hJ hK (i2 A R S)
#align divided_power_algebra.cond_τ DividedPowerAlgebra.Condτ

def CondT (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S],
    ∀ [Algebra A R] [Algebra A S],
      ∀ {I : Ideal R} {J : Ideal S} (hI : DividedPowers I) (hJ : DividedPowers J), Condτ A hI hJ
#align divided_power_algebra.cond_T DividedPowerAlgebra.CondT

end TensorProduct

section free

set_option linter.uppercaseLean3 false
-- hR_free, hS_free are not used for the def (they might be needed at lemmas about cond_T_free)
def CondTFree (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Type u) [CommRing S],
    ∀ [Algebra A R] [Algebra A S],
      ∀ (_ : Module.Free A R) (_ : Module.Free A S),
        ∀ {I : Ideal R} {J : Ideal S} (hI : DividedPowers I) (hJ : DividedPowers J), Condτ A hI hJ
#align divided_power_algebra.cond_T_free DividedPowerAlgebra.CondTFree

/- def cond_Q (A R : Type*) [comm_ring A] [comm_ring R] /- [algebra A R] not used -/
  {I : ideal R} (hI : divided_powers I) : Prop :=
∃ (T : Type*) [comm_ring T], by exactI ∃ [algebra A T], by exactI ∃ [module.free A T]
  {J : ideal T} (hJ : divided_powers J) (f : pd_morphism hI hJ),
  function.surjective f.to_ring_hom
 -/
def CondQ (A : Type u) [CommRing A] : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∀ [Algebra A R] (I : Ideal R) (hI : DividedPowers I),
      ∃ (T : Type u) (_ : CommRing T),
        ∃ (_ : Algebra A T),
          ∃ (_ : Module.Free A T) (f : T →ₐ[A] R) (J : Ideal T) (hJ : DividedPowers J)
            (_ : isDPMorphism hJ hI f), Function.Surjective f
#align divided_power_algebra.cond_Q DividedPowerAlgebra.CondQ

end free

section Proofs

variable {R : Type u} [CommRing R]

open DividedPowerAlgebra

open scoped TensorProduct

/-
variables {M : Type*} [add_comm_group M] [module R M] (h : divided_powers (aug_ideal R M))
(hh : ∀ (x : M) (n : ℕ), h.dpow n (ι R x) = dp R n x)
include M  h -/
-- Roby, lemma 3
set_option linter.uppercaseLean3 false
theorem cond_D_uniqueness [DecidableEq R] {M : Type u} [AddCommGroup M] [Module R M]
    (h : DividedPowers (augIdeal R M)) (hh : ∀ (n : ℕ) (x : M), h.dpow n (ι R M x) = dp R n x)
    {S : Type _} [CommRing S] [Algebra R S] {J : Ideal S} (hJ : DividedPowers J) (f : M →ₗ[R] S)
    (hf : ∀ m, f m ∈ J) : isDPMorphism h hJ (DividedPowerAlgebra.lift hJ f hf) := by
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


/- I have commented out this proof for now because it times out (and since it is quite long, it
  is hard to see where the problem is). -/
-- Roby, lemma 4
theorem T_free_and_D_to_Q (A : Type u) [CommRing A] [DecidableEq A] :
    CondTFree A → CondD A → CondQ A := by
  intro hT_free hD
  simp only [CondQ, CondD, CondTFree] at *
  intro S _ _ I hI

  -- We construct R = A[S] →ₐ[A] S
  let R := MvPolynomial S A
  letI : Algebra R S := RingHom.toAlgebra (MvPolynomial.aeval id).toRingHom
  have mapRS : algebraMap R S = (MvPolynomial.aeval id).toRingHom := RingHom.algebraMap_toAlgebra _
  haveI : IsScalarTower A R S := {
    smul_assoc := fun a r s => by
      simp only [Algebra.smul_def, mapRS]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, _root_.map_mul, AlgHom.commutes]
      rw [← mul_assoc] }

  classical
  let hR := dividedPowersBot R
  let M := ↥I →₀ A
  let f : M →ₗ[A] S := (Basis.constr (Finsupp.basisSingleOne) A) (fun i ↦ (i : S))
  have hf : ∀ p, f p ∈ I := fun p ↦ by
    suffices LinearMap.range f ≤ Submodule.restrictScalars A I by
      apply this
      simp only [LinearMap.mem_range, exists_apply_eq_apply]
    rw [Basis.constr_range]
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [Submodule.coe_restrictScalars, SetLike.mem_coe, SetLike.coe_mem]
  obtain ⟨hM, hM_eq⟩ := hD M
  have hdpM_free : Module.Free A (DividedPowerAlgebra A M) := by
    apply DividedPowerAlgebra.toModule_free
  haveI hR_free : Module.Free A R := Module.Free.of_basis (MvPolynomial.basisMonomials _ _)
  -- We consider `R ⊗[A] DividedPowerAlgebra A M` as a comm ring and an A-algebra
  use R ⊗[A] DividedPowerAlgebra A M, by infer_instance, by infer_instance
  use by infer_instance -- tensor product of free modules is free
  use Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom A R S) (DividedPowerAlgebra.lift hI f hf)
  suffices Condτ A hR hM by
    obtain ⟨hK, _, hM_pd⟩ := this
    use K A ⊥ (augIdeal A M)
    use hK
    constructor
    · rw [← Algebra.range_top_iff_surjective _]
      rw [Algebra.TensorProduct.productMap_range]
      suffices (IsScalarTower.toAlgHom A R S).range = ⊤ by
        rw [this, top_sup_eq]
      rw [Algebra.range_top_iff_surjective]
      simp only [mapRS, IsScalarTower.coe_toAlgHom', AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      exact fun s ↦ ⟨X s, by rw [aeval_X, id.def]⟩
    · suffices hmap_le : _ by
        apply And.intro hmap_le
        intro n a ha
        let ha' := id ha
        simp only [K, Ideal.map_bot, bot_sup_eq] at ha
        simp only [isDPMorphism] at hM_pd
        apply dp_uniqueness hK hI
        simp only [K, Ideal.map_bot, bot_sup_eq]
        · rw [Ideal.map]
        · rintro s ⟨a, ha, rfl⟩
          simp only [i2, Algebra.TensorProduct.includeRight_apply, AlgHom.coe_toRingHom,
            Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
          apply lift_mem_of_mem_augIdeal _ _ _ _ _ _ ha
        · rintro n s ⟨a, ha, rfl⟩
          simp only [SetLike.mem_coe] at ha
          have := hM_pd.2 n a ha
          simp only [AlgHom.coe_toRingHom] at this
          rw [this]
          simp only [i2, Algebra.TensorProduct.includeRight_apply, AlgHom.coe_toRingHom,
            Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
          apply symm
          apply dp_uniqueness hM hI _ (augIdeal_eq_span _ _) _ _ n a ha
          · rintro s ⟨q, hq, m, _, rfl⟩
            change (lift hI f hf) (dp A q m) ∈ I
            rw [liftAlgHom_apply_dp]
            exact hI.dpow_mem (ne_of_gt hq) (hf m)
          · rintro n s ⟨q, hq, m, _, rfl⟩
            change (lift hI f hf) (hM.dpow n (dp A q m)) = hI.dpow n ((lift hI f hf) (dp A q m))
            rw [liftAlgHom_apply_dp, ← hM_eq, hM.dpow_comp n (ne_of_gt hq), hM_eq,
              hI.dpow_comp n (ne_of_gt hq) (hf m)]
            simp only [← nsmul_eq_mul]; rw [map_nsmul]
            rw [liftAlgHom_apply_dp]
            exact ι_mem_augIdeal A M m
        exact ha'
      · rw [K, Ideal.map_bot, bot_sup_eq]
        simp only [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, i2, Algebra.TensorProduct.includeRight_apply,
          AlgHom.coe_toRingHom, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
        apply lift_mem_of_mem_augIdeal
        exact hx
  · -- cond_τ
    apply hT_free
    exact hR_free
    exact hdpM_free
#align divided_power_algebra.T_free_and_D_to_Q DividedPowerAlgebra.T_free_and_D_to_Q

example {A : Type _} [CommRing A] (a : A) (n : ℕ) : n • a = n * a := by refine' nsmul_eq_mul n a

/- In Roby, all PD-algebras A considered are of the form A₀ ⊕ A₊,
where A₊ is the PD-ideal. In other words, the PD-ideal is an augmentation ideal.
Moreover, PD-morphisms map A₀ to B₀ and A₊ to B₊,
so that their kernel is a direct sum K₀ ⊕ K₊

Roby states this as a sory of `pre-graded algebras`,
which correspond to graded algebras by the monoid {⊥, ⊤} with carrier set (fin 0)
or fin 2 (with multiplication)

I am not sure that the proofs can avoid this hypothesis,
especially for tensor products (alas…).

The question is about the formalism to use.
With `is_augmentation_ideal A I`, and `is_augmentation_ideal B J`,
we need to state out the assumption that `f : A →+* B` is homogeneous.

It maps A₊ to B₊ by definition of a PD-morphism,
but A₀ and B₀ are not canonical.
The definition of an augmentation ideal is the existence of
a section A/A₊ →+* A, whose image is A₀.
Write r₀ for the composition A →+* A/A₊ →+* A₀.
The assumptions are : A₊ ≤ r₀.ker, r₀.range ⊓ A₊ = 0

If f is homogeneous (for the two chosen maps r₀), then r₀ (f a) = f (r₀ a)
and f.ker = (f.ker ⊓ A₀) ⊕ (f.ker ⊓ A₊)
or map f I is an augmentation ideal in f.range

This looks less convenient than imposing the graded structure

In lemma 6, we have two surjective algebra morphisms
 f : R →+* R',  g : S →+* S'
and we consider the induced surjective morphism fg : R ⊗ S →+* R' ⊗ S'
R has a PD-ideal I,  R' has a PD-ideal I',
S has a PD-ideal J,  S' has a PD-ideal J'
with assumptions that I' = map f I and J' = map g J,
with quotient PD structures

Lemma 5 has proved that  fg.ker = (f.ker ⊗ 1) ⊔ (1 ⊗ g.ker)

In the end, Roby applies its proposition 4 which we
apparently haven't formalized and make use of yet another definition,
namely of a `divised ideal` :
Up to the homogeneous condition, this is exactly that `K ⊓ I` is a sub-pd-ideal.
The proof of proposition goes by using that
`ideal.span s ⊓ I = ideal.span s ⊓ I`
if `s` is made of homogeneous elements.

So we assume the `roby` condition in the statement, in the hope
that will be possible to prove it each time we apply cond_τ_rel
-/

-- Roby, lemma 6
theorem condτ_rel (A : Type _) [CommRing A] {R S R' S' : Type _} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra A R] [Algebra A S] [Algebra A R'] [Algebra A S']
    (f : R →ₐ[A] R') (hf : Function.Surjective f) {I : Ideal R} (hI : DividedPowers I)
    {I' : Ideal R'} (hI' : DividedPowers I') (hf' : isDPMorphism hI hI' f) (hI'I : I' = I.map f)
    (g : S →ₐ[A] S') (hg : Function.Surjective g) {J : Ideal S} (hJ : DividedPowers J)
    {J' : Ideal S'} (hJ' : DividedPowers J') (hg' : isDPMorphism hJ hJ' g) (hJ'J : J' = J.map g)
    (roby :
      RingHom.ker (Algebra.TensorProduct.map f g) ⊓ k A I J =
        Ideal.map (Algebra.TensorProduct.includeLeft : R →ₐ[A] R ⊗[A] S) (RingHom.ker f ⊓ I) ⊔
          map (Algebra.TensorProduct.includeRight : S →ₐ[A] R ⊗[A] S) (RingHom.ker g ⊓ J))
    (hRS : Condτ A hI hJ) : Condτ A hI' hJ' := by
  obtain ⟨hK, hK_pd⟩ := hRS
  simp only [Condτ]
  let fg := Algebra.TensorProduct.map f g
  sorry
  -- The following line comes from `RobyLemma 5`
  /-let k_fg := Algebra.TensorProduct.ker_tens hf hg
  have s_fg : Function.Surjective fg.toRingHom :=
    sorry --Algebra.TensorProduct.mapSurjective A f hf g hg
  suffices hK_map : k A I' J' = (k A I J).map fg by
    rw [hK_map]
    suffices hK'_pd : isSubDPIdeal hK (RingHom.ker fg.toRingHom ⊓ k A I J) by
      let hK' := DividedPowers.Quotient.OfSurjective.dividedPowers hK s_fg hK'_pd
  use hK'
  constructor
  · -- hI'.is_pd_morphism hK' ↑(i_1 A R' S')
    constructor
    · rw [← hK_map]
      rw [Ideal.map_le_iff_le_comap]; intro a' ha'
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_left; apply Ideal.mem_map_of_mem; exact ha'
    · intro n a' ha'
      suffices ha : a' ∈ f '' I by
        obtain ⟨a, ha, rfl⟩ := ha
      simp only [i1, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeLeft_apply]
      suffices ∀ x : R, fg.toRingHom (x ⊗ₜ[A] 1) = f x ⊗ₜ[A] 1 by rw [← this]
      sorry -- I am not sure what fails here
      sorry
      sorry
      /- rw [Quotient.ofSurjective.dpow_apply hK s_fg]
      have that := hf'.2 n a ha
      simp only [AlgHom.coe_toRingHom] at that ; rw [that]
      rw [← this]
      apply congr_arg
      simp only [← Algebra.TensorProduct.includeLeft_apply]
      exact hK_pd.1.2 n a ha
      · apply Ideal.mem_sup_left; apply Ideal.mem_map_of_mem; exact ha
      · intro x
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul,
          map_one]
      · have := Ideal.image_eq_map_of_surjective f.to_ring_hom I _
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
        rw [this]; rw [hI'I] at ha' ; exact ha'
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact hf -/
  · -- hJ'.is_pd_morphism hK' ↑(i_2 A R' S')
    constructor
    · rw [← hK_map]
      rw [Ideal.map_le_iff_le_comap]; intro a' ha'
      rw [Ideal.mem_comap]
      apply Ideal.mem_sup_right; apply Ideal.mem_map_of_mem; exact ha'
    · intro n a' ha'
      sorry
      /- suffices ha : a' ∈ g '' J; obtain ⟨a, ha, rfl⟩ := ha
      simp only [i2, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]
      suffices : ∀ y : S, fg.toRingHom (1 ⊗ₜ[A] y) = 1 ⊗ₜ[A] g y; rw [← this]
      rw [Quotient.ofSurjective.dpow_apply hK s_fg]
      have that := hg'.2 n a ha
      simp only [AlgHom.coe_toRingHom] at that ; rw [that]
      rw [← this]
      apply congr_arg
      simp only [← Algebra.TensorProduct.includeRight_apply]
      exact hK_pd.2.2 n a ha
      · apply Ideal.mem_sup_right; apply Ideal.mem_map_of_mem; exact ha
      · intro x
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul,
          map_one]
      · have := Ideal.image_eq_map_of_surjective g.to_ring_hom J _
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
        rw [this]; rw [hJ'J] at ha' ; exact ha'
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact hg -/
  · -- ring_hom.ker fg is a “divised ideal”
    change isSubDPIdeal hK (RingHom.ker (Algebra.TensorProduct.map f g) ⊓ k A I J)
    rw [roby]
    apply isSubDPIdeal_sup
    apply isSubDPIdeal_map hI hK hK_pd.1
    exact isSubDPIdeal_ker hI hI' hf'
    apply isSubDPIdeal_map hJ hK hK_pd.2
    exact isSubDPIdeal_ker hJ hJ' hg'
  · -- K A I' J' = map fg (K A I J)
    /- simp only [k, fg, hI'I, hJ'J] -- invalid 'simp', proposition expected ??
    rw [Ideal.map_sup]
    apply congr_arg₂
    change
      map (i_1 A R' S').toRingHom (map f.to_ring_hom I) =
        map (Algebra.TensorProduct.map f g).toRingHom (map (i_1 A R S).toRingHom I)
    simp only [Ideal.map_map]
    apply congr_arg₂ _ _ rfl
    ext x
    simp only [i_1, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul, map_one]
    change
      map (i_2 A R' S').toRingHom (map g.to_ring_hom J) =
        map (Algebra.TensorProduct.map f g).toRingHom (map (i_2 A R S).toRingHom J)
    simp only [Ideal.map_map]
    apply congr_arg₂ _ _ rfl
    ext x
    simp only [i_2, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, AlgHom.coe_toRingHom,
      Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      map_one] -/
    sorry-/
#align divided_power_algebra.cond_τ_rel DividedPowerAlgebra.condτ_rel

-- Roby, lemma 7
theorem condQ_and_condTFree_imply_condT (A : Type _) [CommRing A] (hQ : CondQ A)
    (hT_free : CondTFree A) : CondT A :=
  by
  intro R' _ S' _ _ _ I' J' hI' hJ'
  -- new universe issue
  obtain ⟨R, hR⟩ := hQ R' I' hI'
  sorry
#align divided_power_algebra.cond_Q_and_cond_T_free_imply_cond_T
  DividedPowerAlgebra.condQ_and_condTFree_imply_condT

-- Roby, lemma 8
theorem condT_and_condD_imply_cond_D' (A : Type _) [CommRing A] [DecidableEq A]
    (R : Type _) [CommRing R]  [DecidableEq R] [Algebra A R] (hT : CondT A) (hD : CondD A) :
    CondD R :=
  sorry
#align divided_power_algebra.cond_T_and_cond_D_imply_cond_D'
  DividedPowerAlgebra.condT_and_condD_imply_cond_D'

-- Roby, lemma 9 is in roby9
-- Roby, lemma 10
theorem condT_implies_cond_T'_free (A : Type _) [CommRing A] (R : Type _) [CommRing R] [Algebra A R]
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

theorem condQ_int : CondQ ℤ :=
  T_free_and_D_to_Q ℤ condTFree_int condD_int
#align divided_power_algebra.cond_Q_int DividedPowerAlgebra.condQ_int

theorem condT_int : CondT ℤ :=
  condQ_and_condTFree_imply_condT ℤ condQ_int condTFree_int
#align divided_power_algebra.cond_T_int DividedPowerAlgebra.condT_int

theorem condD_holds (A : Type _) [CommRing A] [DecidableEq A] : CondD A :=
  condT_and_condD_imply_cond_D' ℤ A condT_int condD_int
#align divided_power_algebra.cond_D_holds DividedPowerAlgebra.condD_holds

theorem condTFree_holds (A : Type _) [CommRing A] : CondTFree A :=
  condT_implies_cond_T'_free ℤ A condT_int
#align divided_power_algebra.cond_T_free_holds DividedPowerAlgebra.condTFree_holds

theorem condQ_holds (A : Type _) [CommRing A] [DecidableEq A] : CondQ A :=
  T_free_and_D_to_Q A (condTFree_holds A) (condD_holds A)
#align divided_power_algebra.cond_Q_holds DividedPowerAlgebra.condQ_holds

theorem condT_holds (A : Type _) [CommRing A] [DecidableEq A] : CondT A :=
  condQ_and_condTFree_imply_condT A (condQ_holds A) (condTFree_holds A)
#align divided_power_algebra.cond_T_holds DividedPowerAlgebra.condT_holds

end Proofs

-- Old names
theorem roby_δ (A : Type _) [CommRing A] [DecidableEq A] (M : Type _) [AddCommGroup M]
    [Module A M] : DividedPowerAlgebra.Condδ A M :=
  condD_holds A M
#align divided_power_algebra.roby_δ DividedPowerAlgebra.roby_δ

set_option linter.uppercaseLean3 false
theorem roby_D (A : Type _) [CommRing A] [DecidableEq A] : DividedPowerAlgebra.CondD A :=
  condD_holds A
#align divided_power_algebra.roby_D DividedPowerAlgebra.roby_D

theorem roby_τ (A R S : Type u) [CommRing A] [DecidableEq A] [CommRing R] [Algebra A R]
    [CommRing S] [Algebra A S]
    {I : Ideal R} {J : Ideal S} (hI : DividedPowers I) (hJ : DividedPowers J) : Condτ A hI hJ :=
  condT_holds A R S hI hJ
#align divided_power_algebra.roby_τ DividedPowerAlgebra.roby_τ

theorem roby_T (A : Type _) [CommRing A] [DecidableEq A] : CondT A :=
  condT_holds A
#align divided_power_algebra.roby_T DividedPowerAlgebra.roby_T

open DividedPowerAlgebra

-- namespace divided_power_algebra
-- Part of Roby65 Thm 1
def dividedPowers' (A : Type u) [CommRing A] [DecidableEq A] (M : Type u) [AddCommGroup M]
    [Module A M] : DividedPowers (augIdeal A M) :=
  sorry --(roby_D A M).some
#align divided_power_algebra.divided_powers' DividedPowerAlgebra.dividedPowers'

theorem dpow_ι (A : Type _) [CommRing A] [DecidableEq A] (M : Type _) [AddCommGroup M] [Module A M]
    (x : M) (n : ℕ) : dpow (dividedPowers' A M) n (ι A M x) = dp A n x :=
  sorry --(roby_D A M).choose_spec n x
#align divided_power_algebra.dpow_ι DividedPowerAlgebra.dpow_ι

theorem dp_comp (A : Type _) [CommRing A] [DecidableEq A] (M : Type _) [AddCommGroup M] [Module A M]
    (x : M) {n : ℕ} (m : ℕ) (hn : n ≠ 0) :
    dpow (dividedPowers' A M) m (dp A n x) = ↑(mchoose m n) * dp A (m * n) x := by
  sorry --erw [← (roby_D A M).choose_spec, dpow_comp _ m hn (ι_mem_aug_ideal A M x), dpow_ι]
#align divided_power_algebra.dp_comp DividedPowerAlgebra.dp_comp

theorem roby_theorem_2 (R : Type _) [CommRing R]  [DecidableEq R] (M : Type _) [AddCommGroup M] [Module R M]
    {A : Type _} [CommRing A] [Algebra R A] {I : Ideal A} (hI : DividedPowers I) {φ : M →ₗ[R] A}
    (hφ : ∀ m, φ m ∈ I) :
    isDPMorphism (dividedPowers' R M) hI (DividedPowerAlgebra.lift hI φ hφ) := by
  apply cond_D_uniqueness
  intro m n
  rw [dpow_ι]
#align divided_power_algebra.roby_theorem_2 DividedPowerAlgebra.roby_theorem_2

#exit

-- TODO: fix the last two theorems
theorem lift'_eq_dp_lift (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Type w) [CommRing S] [DecidableEq S] [Algebra R S] {N : Type w} [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] (f : M →ₗ[R] N) :
    ∃ hφ : ∀ m, ((ι S N).restrictScalars R).comp f m ∈ augIdeal S N,
      lift' R S f =
        DividedPowerAlgebra.lift R M (dividedPowers' S N) (((ι S).restrictScalars R).comp f) hφ :=
  by
  suffices hφ : ∀ m, ((ι S).restrictScalars R).comp f m ∈ aug_ideal S N
  use hφ
  ext a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [p.as_sum]
  simp only [map_sum]
  apply congr_arg₂ _ rfl
  ext
  rw [monomial_eq, Finsupp.prod]
  simp only [MvPolynomial.C_eq_smul_one, Algebra.smul_mul_assoc, one_mul]
  simp only [← mkₐ_eq_mk R (relI R M), map_smul]
  apply congr_arg₂ (· • ·) rfl
  simp only [map_prod]
  apply congr_arg₂ _ rfl
  ext ⟨n, m⟩
  simp only [mkₐ_eq_mk, map_pow]
  apply congr_arg₂ _ _ rfl
  rw [← dp_eq_mk R n m]
  rw [lift'_dp_eq]; rw [liftAlgHom_apply_dp]
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, dpow_ι]
  intro m
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    ι_mem_aug_ideal S N (f m)]
#align divided_power_algebra.lift'_eq_dp_lift DividedPowerAlgebra.lift'_eq_dp_lift

--#check lift'_eq_dp_lift
theorem roby_prop_8 (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (S : Type u) [CommRing S] [Algebra R S] {N : Type u} [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) :
    isDPMorphism (dividedPowers' R M) (dividedPowers' S N) (DividedPowerAlgebra.lift' R S f) :=
  by
  let φ := ((ι S).restrictScalars R).comp f
  suffices hφ : ∀ m, φ m ∈ aug_ideal S N
  have roby := roby_theorem_2 R M (divided_powers' S N) hφ
  suffices : lift R M (divided_powers' S N) φ hφ = lift' R S f
  rw [this] at roby ; exact roby
  obtain ⟨hφ', phφ'⟩ := lift'_eq_dp_lift R S f
  rw [phφ']
  intro m
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    ι_mem_aug_ideal S N (f m)]
#align divided_power_algebra.roby_prop_8 DividedPowerAlgebra.roby_prop_8

end DividedPowerAlgebra

end Roby

/-
and a divided power structure on that ideal such that
dpow R n (ι R x) = mk_alg_hom R (rel R M) (X (x, n))

(x,n) represents dpow n x
dpow m (x,n) should be dpow m (dpow n x) = (mchoose m n) dpow (m*n) x
An element x in divided_power_algebra R M takes the form
mk_alg_hom R (rel R M) (P)
where P is a sum of monomials  a * (m,n)   : m ∈ M, n ∈ ℕ
define
dpow k x = sum products a ^ kᵢ * dpow (mchoose kᵢ nᵢ (mᵢ,nᵢ * kᵢ))
where the sum is over functions → ℕ, with sum k
-/
-- Prove that it is unique…
/- Introduce notation ?
Here : x ^ [n] = mk_alg_hom R _ (X (x, n))
In general, x ^ [n]  for dpow n x ?

-/
