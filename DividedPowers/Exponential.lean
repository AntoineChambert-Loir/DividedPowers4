/- Copyright  ACL and MIdFF, 2024 -/

import DividedPowers.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Exponential

/-! # Divided powers and exponential power series -/

namespace DividedPowers

open PowerSeries

variable {R : Type*} [CommRing R] {I : Ideal R}

theorem isExponential_dpowExp (hI : DividedPowers I) {a : R} (ha : a ∈ I) :
    PowerSeries.IsExponential (dpowExp hI a) := by
  rw [isExponential_iff]
  constructor
  · simp only [dpowExp, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, dpow_zero _ ha]
  · intro p q
    simp only [dpowExp, coeff_mk, hI.dpow_mul p q ha]

def exp (hI : DividedPowers I) (a : I) : ExponentialModule R :=
  ⟨hI.dpowExp a, hI.isExponential_dpowExp a.prop⟩

def coe_exp (hI : DividedPowers I) (a : I) :
  ↑(hI.exp a : R⟦X⟧) = hI.dpowExp ↑a := rfl

def exp_add (hI : DividedPowers I) (a b : I) :
    hI.exp (a + b) = hI.exp a + hI.exp b := by
  apply ofExponentialModule_injective
  simp only [coe_exp, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, ofExponentialModule_add]
  rw [hI.add_dpowExp a.prop b.prop]

/- It remains to show that an additive map like exp : I →+ ExponentialModule R furnishes a partial divided power structure -/
end DividedPowers
