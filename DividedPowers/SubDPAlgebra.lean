/- ACL and MIdFF, 2024
-/

import DividedPowers.Basic

/-! Sub DP Algebras -/

variable (A : Type*) [CommSemiring A]
  {R : Type*} [CommRing R] [Algebra A R]
  {I : Ideal R} (hI : DividedPowers I)

/-- A subring is a subDPring if it contains the divided powers of its elements -/
structure SubDPRing extends Subring R where
  dpow_mem' : ∀ n ≠ 0, ∀ a ∈ carrier, a ∈ I → hI.dpow n a ∈ carrier

theorem SubDPRing.dpow_mem (S : SubDPRing hI) {n} (hn : n ≠ 0)
    {a : S.toSubring} (ha : (a : R) ∈ I) :
    hI.dpow n a ∈ S.toSubring := S.dpow_mem' n hn a a.coe_prop ha

/-- A subring is a subDPring if it contains the divided powers of its elements -/
structure SubDPAlgebra extends Subalgebra A R where
  dpow_mem' : ∀ n ≠ 0, ∀ a ∈ carrier, a ∈ I → hI.dpow n a ∈ carrier

theorem SubDPAlgebra.dpow_mem (S : SubDPAlgebra A hI) {n} (hn : n ≠ 0)
    {a : S.toSubalgebra} (ha : (a : R) ∈ I) :
    hI.dpow n a ∈ S.toSubalgebra := S.dpow_mem' n hn a a.coe_prop ha

example (S : Subring R) : Ideal S := I.comap S.subtype

example (S : SubDPRing hI) : DividedPowers (I.comap S.subtype) where
  dpow n a := ⟨hI.dpow n a, by
    by_cases ha : (a : R) ∈ I
    by_cases hn : n = 0
    · simp only [hn, hI.dpow_zero ha, Subring.one_mem]
    · exact S.dpow_mem hI hn ha
    simp only [hI.dpow_null ha, Subring.zero_mem]⟩
  dpow_null := sorry
  dpow_zero := sorry
  dpow_one := sorry
  dpow_mem := sorry
  dpow_add := sorry
  dpow_smul := sorry
  dpow_mul := sorry
  dpow_comp := sorry
