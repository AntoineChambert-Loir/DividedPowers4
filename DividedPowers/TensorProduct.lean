
import DividedPowers.DPAlgebra.Graded.GradeZero
import DividedPowers.DPAlgebra.PolynomialLaw
import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

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


namespace DividedPowers

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

variable (x : M) (n : ℕ)

open DividedPowers Finset Ideal Ideal.Quotient MvPolynomial RingQuot

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
  apply DividedPowers.ext
  intro n x hx
  suffices x ∈ dpEqualizer hK hK' from ((mem_dpEqualizer_iff _ _).mp this).2 n
  suffices h_ss : K A I J ≤ dpEqualizer hK hK' from h_ss hx
  exact sup_le_iff.mpr ⟨le_equalizer_of_isDPMorphism hI _ le_sup_left hK hK' hIK hIK',
    le_equalizer_of_isDPMorphism hJ _ le_sup_right hK hK' hJK hJK'⟩

-- Probably don't need this case
def onTensorProduct_dividedPowers (hI_aug : I.IsAugmentation R) (hJ_aug : J.IsAugmentation S) :
    DividedPowers (K A I J) := by
  sorry

end TensorProduct

section IntFree

variable {R : Type u} [CommRing R]
  {I : Ideal R} (hI : DividedPowers I) {S : Type u} [CommRing S]
  {J : Ideal S} (hJ : DividedPowers J) [CharZero R] [IsDomain R] [CharZero S] [IsDomain S]

-- Generalize the argument in `CharZero` section of `DPow` file.

def onTensorProduct_dividedPowers_of_free (hI_aug : I.IsAugmentation R)
    (hJ_aug : J.IsAugmentation S) : DividedPowers (K ℤ I J) := by

  sorry


end IntFree
-- Ideal.IsAugmentation R I
