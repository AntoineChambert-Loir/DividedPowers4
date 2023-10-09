/- Copyright ACL and MIdFF 
! This file was ported from Lean 3 source module divided_powers.ring
-/
import Oneshot.DividedPowers.Basic

-- import algebra.ring
class DividedPowerRing (A : Type _) extends CommRing A where
  dpIdeal : Ideal A
  dpow : ℕ → pd_ideal → A
  dpow_zero : dpow 0 = 1
  dpow_one : dpow 1 = coe
  dpow_mem : ∀ (n : ℕ) (x : pd_ideal), 1 ≤ n → dpow n x ∈ pd_ideal
  dpow_sum :
    ∀ (n : ℕ) (x y : pd_ideal),
      dpow n (x + y) = Finset.sum (Finset.range (n + 1)) fun k => dpow k x * dpow (n - k) y
  dpow_smul : ∀ (n : ℕ) (a : A) (x : pd_ideal), dpow n (a • x) = a ^ n * dpow n x
  dpow_mul : ∀ (m n : ℕ) (x : pd_ideal), dpow m x * dpow n x = Nat.choose (n + m) m * dpow (m + n) x
  dpow_comp :
    ∀ (m n : ℕ) (hn : 1 ≤ n) (x : pd_ideal),
      dpow m ⟨dpow n x, dpow_mem n x hn⟩ = mchoose m n * dpow (m * n) x
#align divided_power_ring DividedPowerRing

variable {A : Type _} [CommRing A] [hA : DividedPowerRing A] [hA' : DividedPowerRing A]

--notation `(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := pd_morphism hI hJ
structure IsPdMorphism' {A B : Type _} [hA : DividedPowerRing A] [hB : DividedPowerRing B]
    (f : A →+* B) where
  ideal_comp : ∀ a : hA.dpIdeal, f a ∈ hB.dpIdeal
  dpow_comp :
    ∀ (n : ℕ) (a : hA.dpIdeal),
      DividedPowerRing.dpow n ⟨f a, ideal_comp a⟩ = f (DividedPowerRing.dpow n a)
#align is_pd_morphism' IsPdMorphism'

