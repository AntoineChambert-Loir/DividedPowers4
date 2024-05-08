import DividedPowers.ForMathlib.MvPowerSeries.Substitutions

section complements

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommSemiring R]

@[simp]
lemma MvPolynomial.coe_smul (φ : MvPolynomial σ R) (r : R) :
  (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

@[simp]
lemma Polynomial.coe_smul (φ : Polynomial R) (r : R) :
  (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl

@[simp]
theorem PowerSeries.constantCoeff_smul (a : R) (f : PowerSeries R) :
    PowerSeries.constantCoeff R (a • f) = a • PowerSeries.constantCoeff R f :=
  rfl

@[simp]
theorem MvPowerSeries.constantCoeff_smul (a : R) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff σ R (a • f) = a • MvPowerSeries.constantCoeff σ R f :=
  rfl

end complements

section IsExponential

namespace PowerSeries

open MvPowerSeries

variable {R : Type*} [CommRing R]

/-- A power series f : R⟦X⟧ is exponential if f(X + Y) = f(X) f(Y) and f(0) = 1 -/
structure IsExponential (f : R⟦X⟧) : Prop where
  add_mul : subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f
    = subst (MvPowerSeries.X 0) f * PowerSeries.subst (MvPowerSeries.X 1) f
  constantCoeff : constantCoeff R f = 1

/-- The unit power series is exponential -/
theorem isExponential_one : IsExponential (1 : R⟦X⟧) where
  add_mul := by
    rw [← Polynomial.coe_one]
    rw [subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    rw [subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    rw [subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    simp only [map_one, mul_one]
  constantCoeff := by simp only [map_one]

/-- If f and g are exponential, then so is f * g -/
theorem isExponential_mul {f g : PowerSeries R}
    (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) where
  add_mul := by
    repeat
      rw [coe_subst (substDomain_of_constantCoeff_zero (by simp))]
    simp only [map_mul, ← coe_subst, hf.add_mul, hg.add_mul]
    ring
  constantCoeff := by simp only [map_mul, hf.constantCoeff, hg.constantCoeff, mul_one]

/-- If `f` is exponential and n : ℕ`, then `f ^ n` is exponential -/
theorem isExponential_npow {f : R⟦X⟧} (hf : IsExponential f) (n : ℕ) :
    IsExponential (f ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, pow_zero]
    exact isExponential_one
  | succ n hn =>
    rw [pow_succ]
    exact isExponential_mul hn hf

/-- If f is exponential, then f(r T) is exponential, for any r : R -/
theorem isExponential_scale (r : R) {f : PowerSeries R} (hf : IsExponential f) :
    IsExponential (scale r f) where
  constantCoeff := by
    rw [← coeff_zero_eq_constantCoeff, coeff_scale]
    simp only [pow_zero, coeff_zero_eq_constantCoeff, smul_eq_mul, one_mul, hf.constantCoeff]
  add_mul := by
    rw [subst_linear_subst_scalar_comm]
    rw [subst_linear_subst_scalar_comm]
    rw [subst_linear_subst_scalar_comm]
    simp only [MvPowerSeries.scale_eq_substAlgHom, ← map_mul,
      hf.add_mul]
    -- we prove the hypothesis of the last two applications of subst_linear_subst_scalar_comm
    repeat
      intro d hd
      simp only [Fin.isValue, map_add, MvPowerSeries.coeff_X]
      rw [if_neg]
      intro hd'
      apply hd
      rw [hd']
      simp only [Fin.isValue, Finsupp.sum_single_index]
    -- the first application of subst_linear_subst_scalar_comm is a bit different
    · intro d hd
      simp only [Fin.isValue, map_add, MvPowerSeries.coeff_X]
      split_ifs with h0 h1 h1
      · rw [h1, Finsupp.single_left_inj (by norm_num)] at h0
        exfalso; exact one_ne_zero h0
      · exfalso; apply hd
        simp only [h0, Fin.isValue, Finsupp.sum_single_index]
      · exfalso; apply hd
        simp only [h1, Fin.isValue, Finsupp.sum_single_index]
      · simp only [add_zero]

theorem isExponential_scale_add (r s : R) {f : R⟦X⟧} (hf : IsExponential f) :
    scale (r + s) f = scale r f * scale s f := by
  let a : Fin 2 → PowerSeries R
  | 0 => r • X
  | 1 => s • X
  have ha : MvPowerSeries.SubstDomain a := by
    apply MvPowerSeries.substDomain_of_constantCoeff_zero
    intro i
    simp only [X, a]
    match i with
    | 0 =>
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
    | 1 =>
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hf' := congr_arg (MvPowerSeries.subst a) hf.add_mul
  simp only [PowerSeries.subst] at hf'
  rw [ MvPowerSeries.coe_subst ha, map_mul] at hf'
  simp only [← MvPowerSeries.coe_subst] at hf'
  rw [MvPowerSeries.subst_comp_subst_apply _ ha] at hf'
  rw [MvPowerSeries.subst_comp_subst_apply _ ha] at hf'
  rw [MvPowerSeries.subst_comp_subst_apply _ ha] at hf'
  simp only [scale_eq_subst, subst]
  convert hf'
  repeat
    simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_add,
      MvPowerSeries.subst_coe ha]
    simp only [Fin.isValue, map_add, MvPolynomial.aeval_X, add_smul]
  all_goals
    apply MvPowerSeries.substDomain_of_constantCoeff_zero
    intro _
    simp only [Fin.isValue, map_add, MvPowerSeries.constantCoeff_X, add_zero, MvPolynomial.coe_X]

open Additive

noncomputable instance : SMul R (Additive R⟦X⟧) where
  smul r f := ofMul.toFun (scale r (toMul f))

lemma toAdditive_smul_coe (r : R) (f : R⟦X⟧) :
  r • (ofMul f) = ofMul (scale r f) := rfl

lemma toAdditive_smul_coe' (r : R) (f : Additive R⟦X⟧) :
  toMul (r • f) = scale r (toMul f) := rfl

noncomputable instance : DistribMulAction R (Additive R⟦X⟧) where
  one_smul := by
    simp only [Additive.forall, toAdditive_smul_coe, scale_one, AlgHom.coe_id,
      id_eq, forall_const]
  mul_smul := by
    simp only [Additive.forall, toAdditive_smul_coe, ← scale_comp,
      AlgHom.coe_comp, Function.comp_apply, forall_const]
  smul_zero a := by
    rw [← ofMul_one, toAdditive_smul_coe, scale_eq_substAlgHom, map_one]
  smul_add := by
    simp only [Additive.forall, toAdditive_smul_coe, ← ofMul_mul,
      scale_eq_substAlgHom, map_mul, forall_const]

variable (R) in
/-- The R-module of exponential power series f ∈ R⟦X⟧
  satisfying f(X+Y) = f(X) f(Y) and f(0) = 1.
  The addition law is the multiplication of power series
  The scalar multiplication law is given by `PowerSeries.scale` -/
def ExponentialModule : AddSubmonoid (Additive R⟦X⟧) where
  carrier := { f : Additive (R⟦X⟧) | IsExponential (toMul f) }
  add_mem' {f g} hf hg := by
    rw [Set.mem_setOf_eq, toMul_add]
    exact isExponential_mul hf hg
  zero_mem' := by
    simp only [Set.mem_setOf_eq, toMul_zero]
    exact isExponential_one

def memExponentialModule_iff (f : Additive R⟦X⟧) :
    f ∈ ExponentialModule R ↔ IsExponential (toMul f) := by
  simp only [ExponentialModule, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

noncomputable instance instExponentialModule_smul :
    SMul R (ExponentialModule R) where
  smul r f := ⟨r • (f : Additive R⟦X⟧), by
    simp only [memExponentialModule_iff, toAdditive_smul_coe']
    exact isExponential_scale r f.prop⟩

theorem ExponentialModule.coe_smul (r : R) (f : ExponentialModule R) :
  (r • f : ExponentialModule R) = r • (f : Additive R⟦X⟧) := rfl

noncomputable instance instExponentialModule_module :
    Module R (ExponentialModule R) where
  one_smul f := by rw [← Subtype.coe_inj, ExponentialModule.coe_smul, one_smul]
  mul_smul r s f := by
    rw [← Subtype.coe_inj]
    simp only [ExponentialModule.coe_smul, mul_smul]
  smul_zero r := by
    rw [← Subtype.coe_inj, ExponentialModule.coe_smul, ZeroMemClass.coe_zero, smul_zero]
  smul_add r f g := by
    rw [← Subtype.coe_inj]
    simp only [ExponentialModule.coe_smul, AddSubmonoid.coe_add, smul_add]
  add_smul r s f := by
    rw [← Subtype.coe_inj]
    simp only [ExponentialModule.coe_smul, AddSubmonoid.coe_add]
    apply Additive.toMul.injective
    simp only [toAdditive_smul_coe', toMul_add]
    exact isExponential_scale_add r s f.prop
  zero_smul f := by
    rw [← Subtype.coe_inj, ExponentialModule.coe_smul]
    simp only [ZeroMemClass.coe_zero]
    apply Additive.toMul.injective
    simp only [toAdditive_smul_coe', scale_zero_apply, toMul_zero, f.prop.constantCoeff, map_one]
