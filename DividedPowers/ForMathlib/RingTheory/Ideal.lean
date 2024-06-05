import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

-- TODO : check whether we really need that
theorem Ideal.image_eq_map_of_surjective
    {A B : Type _} [Semiring A] [Semiring B] (f : A →+* B)
    (I : Ideal A) (hf : Function.Surjective f) :
    f '' I = I.map f := by
  symm
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  apply Ideal.mem_map_iff_of_surjective _ hf
