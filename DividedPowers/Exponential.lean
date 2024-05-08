/- Copyright  ACL and MIdFF, 2024 -/

import DividedPowers.Basic
import DividedPowers.ForMathlib.MvPowerSeries.Exponential

/-! # Divided powers and exponential power series -/

namespace DividedPowers

open PowerSeries ExponentialModule

variable {R : Type*} [CommRing R] {I : Ideal R}

theorem isExponential_dpowExp (hI : DividedPowers I) {a : R} (ha : a ∈ I) :
    PowerSeries.IsExponential (hI.dpowExp a) := by
  rw [isExponential_iff]
  constructor
  · simp only [dpowExp, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, dpow_zero _ ha]
  · intro p q
    simp only [dpowExp, coeff_mk, hI.dpow_mul p q ha]

def dpowExp_smul (hI : DividedPowers I) {r a : R} (ha : a ∈ I) :
    hI.dpowExp (r * a) = scale r (hI.dpowExp a) := by
  ext n
  simp only [dpowExp, coeff_mk, hI.dpow_smul n ha, coeff_scale, smul_eq_mul]

def exp (hI : DividedPowers I) (a : I) : ExponentialModule R :=
  ⟨hI.dpowExp a, hI.isExponential_dpowExp a.prop⟩

def coe_exp (hI : DividedPowers I) (a : I) :
  ↑(hI.exp a : R⟦X⟧) = hI.dpowExp ↑a := rfl

def exp_LinearMap (hI : DividedPowers I) : I →ₗ[R] ExponentialModule R where
  toFun := hI.exp
  map_add' := fun a b ↦ by
    apply coe_injective
    simp only [coe_exp, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, coe_add]
    rw [hI.add_dpowExp a.prop b.prop]
  map_smul' := fun r a ↦ by
    simp only [RingHom.id_apply]
    apply coe_injective
    simp only [coe_exp, coe_smul]
    simp only [SetLike.val_smul, smul_eq_mul, hI.dpowExp_smul a.prop]

/- It remains to show that an additive map like exp : I →+ ExponentialModule R furnishes a partial divided power structure -/

open Classical in
noncomputable def ofExp (e : I →ₗ[R] ExponentialModule R)
    (coeff_one : ∀ a, coeff R 1 ↑(e a) = a)
    (coeff_mem : ∀ a {n} (_ : n ≠ 0), coeff R n ↑(e a) ∈ I)
    (coeff_comp : ∀ a m {n} (hn : n ≠ 0),
      coeff R m (e ⟨coeff R n (e a), coeff_mem a hn⟩)
        = mchoose m n * coeff R (m * n) (e a)) :
    DividedPowers I where
  dpow n a := if ha : a ∈ I then coeff R n (toPowerSeries (e ⟨a, ha⟩)) else 0
  dpow_null {n a} ha := by simp only [dif_neg ha]
  dpow_zero {a} ha := by
    simp only [dif_pos ha, coeff_zero_eq_constantCoeff_apply, constantCoeff_coe]
  dpow_one {a} ha := by simp only [dif_pos ha, coeff_one]
  dpow_mem {n a} hn ha := by
    simp only [dif_pos ha]
    exact coeff_mem _ hn
  dpow_add n {a b} ha hb := by
    simp only [dif_pos (I.add_mem ha hb), dif_pos ha, dif_pos hb]
    have : e ⟨a + b, I.add_mem ha hb⟩ = e ⟨a, ha⟩ + e ⟨b, hb⟩ := by
      rw [← LinearMap.map_add]
      rfl
    rw [← coe_inj, coe_add, PowerSeries.ext_iff] at this
    rw [this n, coeff_mul]
  dpow_smul n {r a} ha := by
    simp only [dif_pos ha, dif_pos (I.mul_mem_left r ha)]
    have : (⟨r * a, I.mul_mem_left r ha⟩ : I) = r • ⟨a, ha⟩ := rfl
    rw [this, map_smul, coe_smul, coeff_scale, smul_eq_mul]
  dpow_mul m n {a} ha := by simp only [dif_pos ha, add_mul_coe']
  dpow_comp m {n} {a} hn ha := by
    simp only [dif_pos ha, dif_pos (coeff_mem _ hn)]
    exact coeff_comp _ m hn


end DividedPowers
