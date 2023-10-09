-- import Mathlib.Algebra.Algebra.Operations
-- import Mathlib.Data.Rel
-- import Mathlib.Algebra.FreeAlgebra

import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Data.MvPolynomial.CommRing


noncomputable section

open Finset MvPolynomial Ideal.Quotient Ideal RingQuot

-- Defining an algebra as a quotient of polynomials
-- Experiments

variable (R : Type u) [CommSemiring R] (M : Type v)

-- A trivial relation is enough to show problems
inductive r : (MvPolynomial M R) → (MvPolynomial M R) → Prop 

set_option trace.profiler true

def Quot_r := RingQuot (r R M)

instance : -- (priority := 999) : 
    Semiring (Quot_r R M) := 
  RingQuot.instSemiring _

/- We have to make the priority of CommSemiring very low, 
  or else the `HasQuotient` instance below takes about 3s. -/
instance : -- (priority := 10) :
    CommSemiring (Quot_r R M) := RingQuot.instCommSemiring _

instance {S : Type w} [CommRing S] : CommRing (Quot_r S M) :=
  RingQuot.instCommRingRingQuotToSemiringToCommSemiring _

instance instAlgebra 
    {R A M} [CommSemiring R] [CommRing A] [Algebra R A] :
    Algebra R (Quot_r A M) :=
  RingQuot.instAlgebraRingQuot _

-- verify there is no diamond
example (R : Type u) [CommRing R] : 
    (algebraNat : Algebra ℕ (Quot_r R M)) = instAlgebra :=
  rfl

instance {R S A M} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] [SMulCommClass R S A] :
    SMulCommClass R S (Quot_r A M)  := 
  RingQuot.instSMulCommClassRingQuot _

instance {R S A M} [CommRing R] [CommRing S] [CommRing A]
    [SMul R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S  (Quot_r A M) :=
  RingQuot.instIsScalarTowerRingQuot _

instance (R : Type u) [CommRing R] (M : Type v) : 
    HasQuotient (Quot_r R M) (Ideal (Quot_r R M)) := 
  Submodule.hasQuotient

example (R : Type u) [CommRing R] (M : Type v) (I : Ideal (Quot_r R M)) : 
    CommRing ((Quot_r R M) ⧸ I) := 
  Quotient.commRing I

count_heartbeats in 
set_option synthInstance.maxHeartbeats 100000 in
set_option trace.profiler true in 
set_option pp.proofs.withType false in
-- This one is still too slow
instance instAlgebra' (
    R M : Type _) [CommRing R] (I : Ideal (Quot_r R M)) : 
    Algebra R ((Quot_r R M) ⧸ I) := 
Quotient.algebra R

/- 
Used 52680 heartbeats, which is less than the current maximum of 200000.

[2.873722s] set_option pp.proofs.withType false in
    instance (R M : Type _) [CommRing R] : HasQuotient (Quot_r R M) (Ideal (Quot_r R M)) :=
      Submodule.hasQuotient
-/

#exit

namespace FreeAlgebra'

variable (R M : Type _) [CommSemiring R]

inductive r : (FreeAlgebra R M) → (FreeAlgebra R M) → Prop 

def Quot_r : Type _ := RingQuot (r R M)

instance : Semiring (Quot_r R M) := RingQuot.instSemiring _

instance instAlgebra {R A M} [CommSemiring R] [CommRing A] [Algebra R A] :
    Algebra R (Quot_r A M) :=
  RingQuot.instAlgebraRingQuotInstSemiring _

-- verify there is no diamond
example (R : Type _) [CommRing R] : (algebraNat : Algebra ℕ (Quot_r R M)) = instAlgebra := rfl

instance {R S A M} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] [SMulCommClass R S A] :
    SMulCommClass R S (Quot_r A M)  :=
  RingQuot.instSMulCommClassRingQuotInstSMulRingQuotInstSMulRingQuot _

instance {R S A M} [CommRing R] [CommRing S] [CommRing A]
    [SMul R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S  (Quot_r A M) :=
  RingQuot.instIsScalarTowerRingQuotInstSMulRingQuotInstSMulRingQuot _

instance {S : Type _} [CommRing S] : Ring (Quot_r S M) :=
  RingQuot.instRing (r S M)

count_heartbeats in 
set_option synthInstance.maxHeartbeats 100000 in
set_option trace.profiler true in 
set_option pp.proofs.withType false in
instance (R M : Type _) [CommRing R] : 
    HasQuotient (Quot_r R M) (Ideal (Quot_r R M)) := 
  Submodule.hasQuotient

/- Used 2905 heartbeats, which is less than the current maximum of 200000.

  [0.127233s] set_option pp.proofs.withType false in
    instance (R M : Type _) [CommRing R] : HasQuotient (Quot_r R M) (Ideal (Quot_r R M)) :=
      Submodule.hasQuotient
-/

end FreeAlgebra'
