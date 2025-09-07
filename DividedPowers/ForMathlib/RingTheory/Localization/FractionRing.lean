import Mathlib.RingTheory.Localization.FractionRing

namespace Localization

variable {R : Type*} [CommRing R] {M : Submonoid R}

-- [Mathlib.RingTheory.Localization.Basic]
theorem r_iff_of_le_nonZeroDivisors (hM : M ≤ nonZeroDivisors R) (a c : R) (b d : M) :
    Localization.r _ (a, b) (c, d) ↔ a * d = b * c  := by
  simp only [Localization.r_eq_r', Localization.r', Subtype.exists, exists_prop, Con.rel_mk]
  refine ⟨?_, fun h ↦ ⟨1, Submonoid.one_mem M, by simpa only [one_mul, mul_comm a] using h⟩⟩
  rintro ⟨u, hu, h⟩
  have hu' : u ∈ nonZeroDivisors R := hM hu
  simp only [mem_nonZeroDivisors_iff, mul_comm] at hu'
  rw [← sub_eq_zero]
  apply hu'
  rwa [mul_sub, sub_eq_zero, mul_comm a]

-- [Mathlib.RingTheory.Localization.FractionRing]
instance {R : Type*} [CommRing R] [DecidableEq R] : DecidableEq (FractionRing R) := by
  intro x y
  apply recOnSubsingleton₂ x y (r := fun x y ↦ Decidable (x = y))
  intro a c b d
  simp only [mk_eq_mk_iff, r_iff_of_le_nonZeroDivisors (le_refl _)]
  infer_instance

end Localization
