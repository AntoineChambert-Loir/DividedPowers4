import Oneshot.ForMathlib.RingTheory.TensorProduct
import Oneshot.DividedPowers.Basic

-- This will be made in dp_algebra 
-- This will be made in dp_algebra
namespace DividedPowers

open scoped TensorProduct

/- 3.7 Lemma. Suppose R is a ring, В and С are R-algebras, and
I ⊆ В and J ⊆ С are augmentation ideals (i.e. there is a section of В → B/I, etc.) 
with P.D. structures γ and δ, respectively. 
Then the ideal К = Ker (В ⊗ С → B/I ⊗ C/J) has a unique P.D. structure ε 
such that (B,I,γ) → (В ⊗ С,К,ε) and
(C,J,δ) → (B ⊗ C,K,ε) are P.D. morphisms. -/
-- Lemma 3.7 of [BO] -> Change to 1.7.1
def dpowTensorProduct (R B C : Type _) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] {I : Ideal B} {J : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIs : Function.HasRightInverse (Ideal.Quotient.mk I))
    (hJs : Function.HasRightInverse (Ideal.Quotient.mk J)) : ℕ → B ⊗[R] C → B ⊗[R] C :=
  sorry
#align divided_powers.dpow_tensor_product DividedPowers.dpowTensorProduct

def dividedPowersTensorProduct (R B C : Type _) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] {I : Ideal B} {J : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J)
    (hIs : Function.HasRightInverse (Ideal.Quotient.mk I))
    (hJs : Function.HasRightInverse (Ideal.Quotient.mk J)) :
    DividedPowers
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J)).toRingHom.ker
    where
  dpow := dpowTensorProduct R B C hI hJ hIs hJs
  dpow_null := sorry
  dpow_zero := sorry
  dpow_one := sorry
  dpow_mem := sorry
  dpow_add := sorry
  dpow_smul := sorry
  dpow_mul := sorry
  dpow_comp := sorry
#align divided_powers.divided_powers_tensor_product DividedPowers.dividedPowersTensorProduct

theorem dividedPowersTensorProduct_unique (R B C : Type _) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] {I : Ideal B} {J : Ideal C} (hI : DividedPowers I)
    (hJ : DividedPowers J) (hIs : Function.HasRightInverse (Ideal.Quotient.mk I))
    (hJs : Function.HasRightInverse (Ideal.Quotient.mk J))
    (hK :
      DividedPowers
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
              (Ideal.Quotient.mkₐ R J)).toRingHom.ker) :
    hK = dividedPowersTensorProduct R B C hI hJ hIs hJs :=
  by
  apply eq_of_eq_on_ideal
  intro n x hx
  sorry
#align divided_powers.divided_powers_tensor_product_unique DividedPowers.dividedPowersTensorProduct_unique

end DividedPowers

