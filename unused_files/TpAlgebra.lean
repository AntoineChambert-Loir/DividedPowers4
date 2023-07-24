import Mathlib.RingTheory.TensorProduct

variable {R : Type _} [CommRing R]

variable {A B : Type _} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

example : Semiring (TensorProduct R A B) := by infer_instance

example : Algebra R (TensorProduct R A B) := by infer_instance

variable {ι : Type _} [AddMonoid ι]

example : AddMonoid Unit :=
  inferInstance

example : AddMonoid (WithTop Unit) :=
  inferInstance

example : WithTop Unit :=
  Unit.unit

example : WithTop Unit :=
  0

example : (0 : WithTop Unit) = Unit.unit :=
  rfl

example : WithTop Unit :=
  ⊤

example : (Unit.unit : WithTop Unit) ≠ (⊤ : WithTop Unit) :=
  WithTop.coe_ne_top

--#check IsUnit.star
--#eval unit.star
