import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A]

set_option profiler true

lemma foo [Algebra A R] (S : Type*) [CommRing S] [Algebra A S] {S₀ : Subalgebra A S}
    {T₀ : Subalgebra A R} (x y : ↥T₀ ⊗[A] ↥S₀) :
    (Algebra.TensorProduct.map T₀.val S₀.val) x + (Algebra.TensorProduct.map T₀.val S₀.val) y =
    (Algebra.TensorProduct.map T₀.val S₀.val) (x + y) := by
  exact Eq.symm (map_add (Algebra.TensorProduct.map T₀.val S₀.val) x y)
