import DividedPowers.PolynomialMap.Graded
import DividedPowers.DpAlgebra.Graded

/- 

The universal homogeneous PolynomialMap from a module to the degree n 
part of its DividedPowerAlgebra 

-/
open scoped TensorProduct

universe u

variable (R : Type u) [CommRing R]
variable (M : Type _) [AddCommGroup M] [Module R M]

/- 
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


def gamma (n : ℕ) : PolynomialMap R M (DividedPowerAlgebra R M) where
  toFun S _ _ := fun m ↦ DividedPowerAlgebra.dp R n m
  isCompat φ := sorry
