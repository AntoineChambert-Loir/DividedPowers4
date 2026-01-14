/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.RingTheory.DividedPowers.Basic
import DividedPowers.ExponentialModule.Basic

/-! # Divided powers and exponential power series

Let `R` be a commutative ring and let `I` be an ideal of `R`.

## Main Definitions

* `DividedPowers.exp'` :  if `hI` is a divided power structure on `I` and `a : I`,
  `hI.exp' a` is the power series `hI.exp a`, as an element of `ExponentialModule R`.

* `DividedPowers.of_exp` : the divided power structure on `I` induced by a linear map
  `I →ₗ[R] ExponentialModule R`.

## Main Results

* `DividedPowers.exp_isExponential` : if `hI` is a divided power structure on `I`, then the
  exponential series `hI.exp` is exponential.

-/

namespace DividedPowers

open PowerSeries Additive

variable {R : Type*} [CommRing R] {I : Ideal R}

theorem exp_isExponential (hI : DividedPowers I) {a : R} (ha : a ∈ I) :
    IsExponential (hI.exp a) :=
  isExponential_iff.mpr ⟨fun p q ↦ by simp only [exp, coeff_mk, hI.mul_dpow ha],
    by simp only [exp, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, dpow_zero _ ha]⟩

lemma exp_smul (hI : DividedPowers I) {r a : R} (ha : a ∈ I) :
    hI.exp (r * a) = rescale r (hI.exp a) := by
  ext n
  simp only [exp, coeff_mk, coeff_rescale, hI.dpow_mul ha]

/-- The power series `hI.exp a`, as an element of `ExponentialModule R`. -/
def exp' (hI : DividedPowers I) (a : I) : ExponentialModule R :=
  ⟨ofMul (hI.exp a), hI.exp_isExponential a.prop⟩

lemma coe_exp' (hI : DividedPowers I) (a : I) :
    (hI.exp' a : R⟦X⟧) = hI.exp ↑a := rfl

open ExponentialModule

/-- The `R`-linear map `hI.exp'` from `I` to `ExponentialModule R`. -/
noncomputable def exp'_linearMap (hI : DividedPowers I) :
    I →ₗ[R] ExponentialModule R where
  toFun := hI.exp'
  map_add' := fun a b ↦ by
    rw [← coe_inj, coe_exp', exp', Submodule.coe_add, coe_add, hI.exp_add a.prop b.prop,
      coe_exp', coe_mk]
  map_smul' := fun r a ↦ by
    rw [RingHom.id_apply, ← coe_inj]
    simp only [coe_exp', SetLike.val_smul, smul_eq_mul, hI.exp_smul a.prop, coe_smul,
      Algebra.algebraMap_self, RingHom.id_apply]

theorem exp'_linearMap_apply (hI : DividedPowers I) (x : I) :
    hI.exp'_linearMap x = hI.exp x := rfl

/- It remains to show that an additive map like exp : `I →+ ExponentialModule R` furnishes a
  partial divided power structure -/

/-- The divided power structure on `I` induced by a linear map `I →ₗ[R] ExponentialModule R`. -/
noncomputable def of_exp [DecidablePred (fun x ↦ x ∈ I)] (e : I →ₗ[R] ExponentialModule R)
    (coeff_one : ∀ a, coeff 1 (e a : R⟦X⟧) = a)
    (coeff_mem : ∀ a {n} (_ : n ≠ 0), coeff n ↑(e a) ∈ I)
    (coeff_comp : ∀ a m {n} (hn : n ≠ 0), coeff m (e ⟨coeff n (e a), coeff_mem a hn⟩) =
      Nat.uniformBell m n * coeff (m * n) (e a : R⟦X⟧)) :
    DividedPowers I where
  dpow n a       := if ha : a ∈ I then coeff n (toPowerSeries (e ⟨a, ha⟩)) else 0
  dpow_null ha   := by simp only [dif_neg ha]
  dpow_zero ha   := by simp only [dif_pos ha, coeff_zero_eq_constantCoeff_apply, constantCoeff_coe]
  dpow_one ha    := by simp only [dif_pos ha, coeff_one]
  dpow_mem hn ha := by simp only [dif_pos ha, coeff_mem _ hn]
  dpow_add n {a b} ha hb := by
    simp only [dif_pos (I.add_mem ha hb), dif_pos ha, dif_pos hb]
    have : e ⟨a + b, I.add_mem ha hb⟩ = e ⟨a, ha⟩ + e ⟨b, hb⟩ := by
      rw [← LinearMap.map_add, AddMemClass.mk_add_mk]
    rw [← coe_inj, coe_add, PowerSeries.ext_iff] at this
    rw [this n, coeff_mul]
  dpow_mul n {r a} ha := by
    simp only [dif_pos ha, dif_pos (I.mul_mem_left r ha)]
    have : (⟨r * a, I.mul_mem_left r ha⟩ : I) = r • ⟨a, ha⟩ := rfl
    rw [this, map_smul, coe_smul, coeff_rescale, Algebra.algebraMap_self, RingHom.id_apply]
  mul_dpow ha := by simp only [dif_pos ha, choose_mul_coeff_add_eq]
  dpow_comp hn ha := by simp only [dif_pos ha, dif_pos (coeff_mem _ hn), coeff_comp _ _ hn]

end DividedPowers
