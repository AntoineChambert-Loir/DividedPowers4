import Mathbin.Algebra.Algebra.Tower
import Mathbin.RingTheory.Localization.FractionRing

def Algebra.comp (R A B : Type _) [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A]
    [Algebra A B] : Algebra R B :=
  (RingHom.comp (algebraMap A B) (algebraMap R A)).toAlgebra
#align algebra.comp Algebra.comp

theorem IsScalarTower.comp (R A B : Type _) [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra A B] : @IsScalarTower R A B _ _ (Algebra.comp R A B).toSMul :=
  {
    smul_assoc := fun r a b => by
      letI : Algebra R B := Algebra.comp R A B
      simp only [Algebra.smul_def, map_mul, mul_assoc]; rfl }
#align is_scalar_tower.comp IsScalarTower.comp

theorem IsScalarTower.comp' (R A B S : Type _) [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [CommSemiring S] [Algebra R A] [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S] :
    @IsScalarTower R B S (Algebra.comp R A B).toSMul _ (Algebra.comp R A S).toSMul :=
  {
    smul_assoc := fun x y z => by
      haveI := IsScalarTower.comp R A B
      haveI := IsScalarTower.comp R A S
      nth_rw 1 [← one_smul A y]
      rw [← one_smul A (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc] }
#align is_scalar_tower.comp' IsScalarTower.comp'

theorem algebraMap_injective' (R A K : Type _) [CommRing R] [Field A] [Algebra R A]
    [IsFractionRing R A] [Field K] [Algebra R K] [Algebra A K] [IsScalarTower R A K] :
    Function.Injective ⇑(algebraMap R K) :=
  by
  rw [IsScalarTower.algebraMap_eq R A K]
  exact Function.Injective.comp (algebraMap A K).Injective (IsFractionRing.injective R A)
#align algebra_map_injective' algebraMap_injective'

