import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Topology.Algebra.Ring.Basic

/-!

# Topological algebras

A topological algebra `S` over a commutative topological ring `R` is an `R`-algebra `S`
which is a topological ring and such that the algebra map from `R` to `S` is continuous.

-/

universe u v

open Set Filter TopologicalSpace Function Topology Filter

section TopologicalAlgebra

/-- A topological algebra `S` over a commutative topological semiring `R` is an `R`-algebra `S`
  which is a topological semiring and such that the algebra map from `R` to `S` is continuous. -/
class TopologicalAlgebra (R : Type u) (A : Type v) [CommSemiring R] [TopologicalSpace R]
    [TopologicalSemiring R] [Semiring A] [TopologicalSpace A] [TopologicalSemiring A] extends
    Algebra R A where
  continuous_algebraMap : Continuous (algebraMap R A)

variable (R : Type u) (A : Type v) [CommSemiring R] [TopologicalSpace R]
    [TopologicalSemiring R] [Semiring A] [TopologicalSpace A] [TopologicalSemiring A]

/- This gives the error: cannot find synthesization order for instance instContinuousAddToAddToDistribToNonUnitalNonAssocSemiringToNonUnitalNonAssocRingToNonAssocRing with type
  ∀ (R : Type u) (A : Type v) [inst : CommRing R] [inst_1 : TopologicalSpace R] [inst_2 : TopologicalRing R]
    [inst_3 : Ring A] [inst_4 : TopologicalSpace A] [inst_5 : TopologicalRing A] [inst : TopologicalAlgebra R A],
    ContinuousAdd A
all remaining arguments have metavariables:
  CommRing ?R
  TopologicalSpace ?R
  @TopologicalRing ?R ?inst✝ NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing
  @TopologicalAlgebra ?R A ?inst✝ ?inst✝¹ ?inst✝² inst✝³ inst✝² inst✝¹
-/
--instance [TopologicalAlgebra R A] : ContinuousAdd A := sorry

-- But if we put `TopologicalAlgebra R A` as a variable, it is fine.
example : ContinuousAdd A := inferInstance

/-- If `R` is a discrete topological ring,
  then any topological ring `S` which is an `R`-algebra
  is also a topological `R`-algebra. -/
instance (priority := 50) DiscreteTopology.topologicalAlgebra
    [DiscreteTopology R] [Algebra R A] :
    TopologicalAlgebra R A :=
  { (inferInstance : Algebra R A) with
    continuous_algebraMap := continuous_of_discreteTopology }

namespace Subalgebra

variable [TopologicalAlgebra R A]
/-- An `R`-subalgebra `S` of `A` is a topological algebra (with the subspace topology). -/
instance topologicalAlgebra (S : Subalgebra R A) :
    TopologicalAlgebra R S where
  continuous_algebraMap := by
    rw [inducing_subtype_val.continuous_iff]
    suffices Subtype.val ∘ (algebraMap R S) = algebraMap R A by
      erw [this]
      exact TopologicalAlgebra.continuous_algebraMap
    rfl

-- What follows seems to be in Mathlib.Topology.Algebra.Algebra

/-
/-- The (topological-space) closure of a subalgebra of a topological algebra is
itself a subalgebra. -/
def topologicalClosure (S : Subalgebra R A) : Subalgebra R A :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (S : Set A)
    algebraMap_mem' := fun r => subset_closure (algebraMap_mem S r) }

@[simp]
theorem topologicalClosure_coe (S : Subalgebra R A) :
    (S.topologicalClosure : Set A) = _root_.closure (S : Set A) :=
  rfl

theorem le_topologicalClosure (S : Subalgebra R A) : S ≤ S.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (S : Subalgebra R A) :
    IsClosed (S.topologicalClosure : Set A) := isClosed_closure

theorem topologicalClosure_minimal (S : Subalgebra R A) {T : Subalgebra R A} (h : S ≤ T)
    (hT : IsClosed (T : Set A)) : S.topologicalClosure ≤ T :=
  closure_minimal h hT

/-- If a subalgebra of a topological semiring is commutative, then so is its
topological closure. -/
def commSemiringTopologicalClosure [T2Space A] (S : Subalgebra R A)
    (hS : ∀ x y : S, x * y = y * x) : CommSemiring S.topologicalClosure :=
  { (S.topologicalClosure R A).toSemiring, S.toSubmonoid.commMonoidTopologicalClosure hS with }
-/

end Subalgebra

section Prod

/-- The product topology on the cartesian product of two topological algebras
  makes the product into a topological algebra. -/
instance [TopologicalAlgebra R A]
    {B : Type*} [Semiring B] [TopologicalSpace B] [TopologicalSemiring B]
    [TopologicalAlgebra R B] : TopologicalAlgebra R (A × B) :=
{ (inferInstance : Algebra R (A × B)) with
  continuous_algebraMap := continuous_prod_mk.mpr
    ⟨TopologicalAlgebra.continuous_algebraMap, TopologicalAlgebra.continuous_algebraMap⟩ }

end Prod

section Pi

/-- The product topology on the cartesian product of two topological algebras
  makes the product into a topological algebra. -/
instance Pi.topologicalAlgebra {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
  [∀ b, Semiring (C b)] [∀ b, TopologicalSemiring (C b)] [∀ b, TopologicalAlgebra R (C b)] :
  TopologicalAlgebra R (Π b , C b) :=
{ toAlgebra := Pi.algebra _ _
  continuous_algebraMap :=
    continuous_pi_iff.mpr fun _ =>  TopologicalAlgebra.continuous_algebraMap }

end Pi

end TopologicalAlgebra
