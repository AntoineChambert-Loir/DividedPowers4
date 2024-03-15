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
variable (M : Type _) [AddCommGroup M] [Module R M]

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

noncomputable
def gamma (n : ℕ) : PolynomialMap R M (DividedPowerAlgebra R M) where
  toFun' S _ _ := fun m ↦
    (DividedPowerAlgebra.dpScalarExtensionEquiv R S M).symm
      (DividedPowerAlgebra.dp S n m)
  isCompat' φ := sorry
