import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct

variable (R S M N : Type*) [CommRing R] [CommRing S]
variable [CommRing M] [Algebra R M] [Algebra S M] [CommRing N] [Algebra R N]
variable [Algebra R S] [IsScalarTower R S M]

/-
  The most general version `mkₐ_smul_one_tmul_one'` is the "correct" one, but it is the
  slowest one inside the proof where we apply it.

  Main point: `AlgHom.map_smul` (which we were using before) is deprecated, and `map_smul` is
  much slower.
  -/

lemma mkₐ_smul_one_tmul_one' (s : S) {B : Type*} [CommRing B] [Algebra R B]
  [Algebra S B] [IsScalarTower R S B] (f : M ⊗[R] N →ₐ[S] B)  :
    f ((s • (1 : M)) ⊗ₜ[R] (1 : N)) = s • (1 : B ) := by
  suffices (s • (1 : M)) ⊗ₜ[R] (1 : N) = s • (1 : M ⊗[R] N) by
    rw [this, map_smul, map_one]
  rfl

lemma mkₐ_smul_one_tmul_one (s : S) (I : Ideal (M ⊗[R] N)) :
    (Ideal.Quotient.mkₐ S I) ((s • (1 : M)) ⊗ₜ[R] (1 : N)) =
      s • (1 : M ⊗[R] N ⧸ I) := by
  suffices (s • (1 : M)) ⊗ₜ[R] (1 : N) = s • (1 : M ⊗[R] N) by
    rw [this, map_smul, map_one]
  rfl
