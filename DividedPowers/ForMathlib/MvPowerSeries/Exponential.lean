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

#exit

-- It sems that all the rest is garbage

lemma foo1 (r : R) {p : MvPowerSeries (Fin 2) R} (hp : SubstDomain p) :
    subst p (r • X : PowerSeries R) = r • p := by
  simp only [subst_smul hp, subst_X hp]


/-
/-- If f is exponential, then f(r T) is exponential, for any r : R -/
theorem IsExponential.smul_v1 (r : R) {f : PowerSeries R} (hf : IsExponential f) :
    IsExponential (PowerSeries.subst (r • (PowerSeries.X : PowerSeries R)) f) where
  constantCoeff := by
    rw [PowerSeries.constantCoeff]
    erw [PowerSeries.constantCoeff_subst (substDomain_of_constantCoeff_zero ?_)]
    rw [finsum_eq_single _ 0]
    · simp only [coeff_zero_eq_constantCoeff, pow_zero, map_one, smul_eq_mul, mul_one, hf.constantCoeff]
    · intro n hn
      simp only [map_pow, smul_eq_mul]
      convert mul_zero _
      convert zero_pow hn
      change PowerSeries.constantCoeff R (r • X) = 0
      simp only [constantCoeff_smul, constantCoeff_X, smul_eq_mul, mul_zero]
    · change PowerSeries.constantCoeff R (r • X) = 0
      simp only [constantCoeff_smul, constantCoeff_X, smul_eq_mul, mul_zero]
  add_mul := by
    rw [subst_comp_subst_apply (substDomain_of_constantCoeff_zero
        (by rw [MvPowerSeries.constantCoeff_smul, X, MvPowerSeries.constantCoeff_X, smul_zero]))
      (substDomain_of_constantCoeff_zero (by simp))]
    rw [subst_comp_subst_apply (substDomain_of_constantCoeff_zero
        (by rw [MvPowerSeries.constantCoeff_smul, X, MvPowerSeries.constantCoeff_X, smul_zero]))
      (substDomain_of_constantCoeff_zero (by simp))]
    rw [subst_comp_subst_apply (substDomain_of_constantCoeff_zero
        (by rw [MvPowerSeries.constantCoeff_smul, X, MvPowerSeries.constantCoeff_X, smul_zero]))
      (substDomain_of_constantCoeff_zero (by simp))]
    rw [foo1 r (substDomain_of_constantCoeff_zero (by simp))]
    rw [← foo2]
    have : MvPowerSeries.subst
      (fun i => r • (MvPowerSeries.X i : MvPowerSeries (Fin 2) R))
      (subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f)
      = subst
          (MvPowerSeries.subst
            (fun i => r • (MvPowerSeries.X i : MvPowerSeries (Fin 2) R))
            (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R))
          f := by
      simp only [subst]
      rw [MvPowerSeries.subst_comp_subst_apply]
      -- two more goals
      exact MvPowerSeries.substDomain_of_constantCoeff_zero (by simp)
      exact MvPowerSeries.substDomain_of_constantCoeff_zero (by simp)
    simp only [← this, hf.add_mul]
    rw [MvPowerSeries.coe_subst
      (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp)),
      map_mul, ← MvPowerSeries.coe_subst]
    simp only [subst]
    rw [MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))
      (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))]
    rw [MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))
      (MvPowerSeries.substDomain_of_constantCoeff_zero (by simp))]
    apply congr_arg₂
    · apply congr_arg₂ _ _ rfl
      apply funext
      intro _
      rw [← MvPolynomial.coe_X, MvPowerSeries.subst_coe, MvPolynomial.aeval_X,
        MvPolynomial.coe_X]
      change _ = PowerSeries.subst (MvPowerSeries.X 0) _
      rw [← Polynomial.coe_X, ← Polynomial.coe_smul, PowerSeries.subst_coe]
      rw [map_smul, Polynomial.aeval_X]
      apply PowerSeries.substDomain_of_constantCoeff_zero (by simp)
      apply MvPowerSeries.substDomain_of_constantCoeff_zero (by simp)
    · apply congr_arg₂ _ _ rfl
      apply funext
      intro _
      rw [← MvPolynomial.coe_X, MvPowerSeries.subst_coe, MvPolynomial.aeval_X,
        MvPolynomial.coe_X]
      change _ = PowerSeries.subst (MvPowerSeries.X 1) _
      rw [← Polynomial.coe_X, ← Polynomial.coe_smul, PowerSeries.subst_coe, map_smul, Polynomial.aeval_X]
      exact PowerSeries.substDomain_of_constantCoeff_zero (by simp)
      exact MvPowerSeries.substDomain_of_constantCoeff_zero (by simp)
    -- l'hypothèse de foo2
    · intro d hd
      simp only [map_add, MvPowerSeries.coeff_X]
      split_ifs with h0 h1 h1
      · rw [h1, Finsupp.single_left_inj (by norm_num)] at h0
        exfalso; exact one_ne_zero h0
      · exfalso; apply hd
        simp only [h0, Fin.isValue, Finsupp.sum_single_index]
      · exfalso; apply hd
        simp only [h1, Fin.isValue, Finsupp.sum_single_index]
      · simp


-/


section ExponentialPowerSeries

/- Works, but is not very nice to use -/
namespace MvPowerSeries

variable (τ : Type*) [DecidableEq τ] (R : Type*) [CommRing R] (f : PowerSeries R)

noncomputable def Dom : Ideal (MvPowerSeries τ R) where
  carrier := setOf PowerSeries.SubstDomain
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

variable {R τ}

def Dom.substDomain (d : Dom τ R) :
    SubstDomain (S := R) (σ := Unit) (fun _ ↦ d.val) := by
  apply substDomain_of_constantCoeff_zero
  intro _
  have := d.prop.const_coeff
  apply?
  -- exact fun _ ↦ d.prop.const_coeff
  -- tendsto_zero := sorry

variable (r : R)

example : (constantCoeff Unit R) (r • X ()) = 0 := by
  erw [MvPowerSeries.coeff_smul]
  simp only [coeff_zero_eq_constantCoeff, constantCoeff_X, mul_zero]

noncomputable def rX : Dom Unit R :=
  ⟨r • MvPowerSeries.X (),
    { const_coeff := by
        erw [MvPowerSeries.coeff_smul]
        simp only [coeff_zero_eq_constantCoeff, constantCoeff_X, mul_zero, IsNilpotent.zero] } ⟩

/- noncomputable def T (i : τ) : Dom τ R :=
  ⟨ ((MvPolynomial.X i : MvPolynomial τ R) : MvPowerSeries τ R),
    { const_coeff := by simp [IsNilpotent.zero] } ⟩
-/

noncomputable def T (i : τ) : Dom τ R :=
  ⟨ (MvPowerSeries.X i : MvPowerSeries τ R),
    { const_coeff := by simp [IsNilpotent.zero] } ⟩

theorem coe_T (i : τ) :
    ((T i : Dom τ R) : MvPowerSeries τ R) = MvPowerSeries.X i :=
  rfl

noncomputable def Dom.subst (a : Dom τ R) :
    MvPowerSeries Unit R →ₐ[R] MvPowerSeries τ R :=
  MvPowerSeries.substAlgHom (Dom.substDomain a)
noncomputable def a : Dom Unit R := T ()
noncomputable def b : Dom (Fin 2) R := T 0 + T 1

--  Dom.subst (T 0 + T 1 : Dom (Fin 2) R) f = Dom.subst (T 0) f * Dom.subst (T 1) f

@[simp]
lemma _root_.MvPolynomial.coe_smul {σ : Type*} {R : Type*} [CommSemiring R]
    (φ : MvPolynomial σ R) (r : R) :
  (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

@[simp]
lemma _root_.Polynomial.coe_smul {R : Type*} [CommSemiring R]
    (φ : Polynomial R) (r : R) :
  (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl

@[simp]
theorem _root_.PowerSeries.constantCoeff_smul
    {R : Type*} [CommSemiring R] (a : R) (f : PowerSeries R) :
    PowerSeries.constantCoeff R (a • f) = a • PowerSeries.constantCoeff R f :=
  rfl

@[simp]
theorem _root_.MvPowerSeries.constantCoeff_smul {σ : Type*}
    {R : Type*} [CommSemiring R] (a : R) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff σ R (a • f) = a • MvPowerSeries.constantCoeff σ R f :=
  rfl

theorem _root_.MvPowerSeries.monomial_eq {R : Type u} {σ : Type u_1} [DecidableEq σ] {a : R} {d : σ →₀ ℕ} [CommSemiring R] :
    (MvPowerSeries.monomial R d) a = MvPowerSeries.C σ R a * Finsupp.prod d fun (n : σ) (e : ℕ) => MvPowerSeries.X n ^ e :=  by
    rw [← MvPolynomial.coe_monomial, MvPolynomial.monomial_eq]
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_C]
    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_finsupp_prod]
    simp only [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]

lemma foo1 (r : R) (p : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst p (r • PowerSeries.X : PowerSeries R) = r • p := by
  simp only [← Polynomial.coe_X, ← Polynomial.coe_smul]
  rw [PowerSeries.subst_coe]
  simp only [map_smul, Polynomial.aeval_X]

lemma foo1_v2 (r : R) :
    PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (r • PowerSeries.X : PowerSeries R)
    = r • MvPowerSeries.X 0 + r • MvPowerSeries.X 1 := by
  simp only [foo1, smul_add]

lemma foo1_v1 (r : R) :
    PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (r • PowerSeries.X : PowerSeries R)
    = r • MvPowerSeries.X 0 + r • MvPowerSeries.X 1 := by
  simp only [← MvPolynomial.coe_X, ← Polynomial.coe_X, ← MvPolynomial.coe_add, ← Polynomial.coe_smul]
  rw [PowerSeries.subst_coe]
  simp only [Fin.isValue, MvPolynomial.coe_add, MvPolynomial.coe_X, map_smul, Polynomial.aeval_X,
    smul_add]

lemma foo2 [DecidableEq σ] [Finite σ] (r : R) (f : MvPowerSeries σ R)
    (hp : ∀ (d : σ →₀ ℕ), (d.sum (fun i n ↦ n) ≠ 1) → coeff R d f = 0) :
    MvPowerSeries.subst (fun i ↦ r • (MvPowerSeries.X (σ := σ) (R := R) i)) f = r • f := by
  have hr : SubstDomain fun s => r • (X s : MvPowerSeries σ R) := {
    const_coeff := fun i ↦ by simp [MvPowerSeries.constantCoeff_smul]
    tendsto_zero := by simp }
  ext e
  rw [coeff_subst hr, finsum_eq_sum _ (coeff_subst_finite hr _ _)]
  simp only [smul_eq_mul, map_smul]
  rw [Finset.sum_eq_single e]
  · rw [mul_comm]
    apply congr_arg₂ _ _ rfl
    simp only [smul_pow]
    simp only [Algebra.smul_def]
    rw [Finsupp.prod_mul, ← map_finsupp_prod, ← Algebra.smul_def, map_smul]
    conv_rhs => rw [← mul_one r]
    rw [smul_eq_mul]
    apply congr_arg₂
    · sorry
    · sorry
  · sorry
  · sorry

lemma foo2_v2 (r : R) :
    MvPowerSeries.subst
      (fun i ↦ r • (MvPowerSeries.X i : MvPowerSeries (Fin 2) R))
      (MvPowerSeries.X 0 + (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) R)
    = r • (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + r • (MvPowerSeries.X 1) := by
  rw [foo2 r (MvPowerSeries.X 0 + MvPowerSeries.X 1) ?_, smul_add]
  intro d hd
  simp only [Fin.isValue, map_add]
  sorry

lemma foo2_v1 (r : R) :
    MvPowerSeries.subst
      (fun i ↦ r • (MvPowerSeries.X i : MvPowerSeries (Fin 2) R))
      (MvPowerSeries.X 0 + (MvPowerSeries.X 1) : MvPowerSeries (Fin 2) R)
    = r • (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) + r • (MvPowerSeries.X 1) := by
  simp only [← MvPolynomial.coe_X, ← Polynomial.coe_X, ← MvPolynomial.coe_add,
    ← MvPolynomial.coe_smul]
  rw [MvPowerSeries.subst_coe]
  simp
  exact {
    const_coeff := fun i ↦ by
      simp [MvPowerSeries.constantCoeff_smul]
    tendsto_zero := by simp only [MvPolynomial.coe_smul, MvPolynomial.coe_X, Filter.cofinite_eq_bot,
      Filter.tendsto_bot] }

/-- If f is exponential, then f(r T) is exponential, for any r : R -/
example (r : R) (f : PowerSeries R) (hf : IsExponential f) :
    IsExponential (PowerSeries.subst (r • (PowerSeries.X : PowerSeries R)) f) := by
  simp only [IsExponential] at hf ⊢
  have := foo1 r
  -- simp only [PowerSeries.subst, PowerSeries.X] at this
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.substDomain_of_constantCoeff_zero
      (by rw [constantCoeff_smul, PowerSeries.X, constantCoeff_X, smul_zero]))
    (PowerSeries.substDomain_of_constantCoeff_zero
      (by simp))]
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.substDomain_of_constantCoeff_zero
      (by rw [constantCoeff_smul, PowerSeries.X, constantCoeff_X, smul_zero]))
    (PowerSeries.substDomain_of_constantCoeff_zero
      (by simp))]
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.substDomain_of_constantCoeff_zero
      (by rw [constantCoeff_smul, PowerSeries.X, constantCoeff_X, smul_zero]))
    (PowerSeries.substDomain_of_constantCoeff_zero
      (by simp))]
  simp only [foo1]
  rw [← foo2]
  set f1 := PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) R) f
  set g := subst (fun i => r • (X i : MvPowerSeries (Fin 2) R)) (X 0 + X 1 : MvPowerSeries (Fin 2) R)
  set f2 := PowerSeries.subst  g f
  have : subst (fun i => r • (X i : MvPowerSeries (Fin 2) R)) f1
    = PowerSeries.subst  g f := by
    simp only [f1, PowerSeries.subst]
    rw [subst_comp_subst_apply]
    -- two more goals
    exact substDomain_of_constantCoeff_zero (by simp)
    exact substDomain_of_constantCoeff_zero (by simp)
  simp only [f2, ← this, hf]
  rw [coe_subst (substDomain_of_constantCoeff_zero (by simp)),
    map_mul, ← coe_subst]
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply
    (substDomain_of_constantCoeff_zero (by simp))
    (substDomain_of_constantCoeff_zero (by simp))]
  rw [subst_comp_subst_apply
    (substDomain_of_constantCoeff_zero (by simp))
    (substDomain_of_constantCoeff_zero (by simp))]
  apply congr_arg₂
  · apply congr_arg₂ _ _ rfl
    apply funext
    intro _
    rw [← MvPolynomial.coe_X, subst_coe, MvPolynomial.aeval_X,
      MvPolynomial.coe_X]
    exact substDomain_of_constantCoeff_zero (by simp)
  · apply congr_arg₂ _ _ rfl
    apply funext
    intro _
    rw [← MvPolynomial.coe_X, subst_coe, MvPolynomial.aeval_X,
      MvPolynomial.coe_X]
    exact substDomain_of_constantCoeff_zero (by simp)
  -- l'hypothèse de foo2
  · intro d hd
    simp only [map_add, coeff_X]
    split_ifs with h0 h1 h1
    · rw [h1, Finsupp.single_left_inj (by norm_num)] at h0
      exfalso; exact one_ne_zero h0
    · exfalso; apply hd
      simp only [h0, Fin.isValue, Finsupp.sum_single_index]
    · exfalso; apply hd
      simp only [h1, Fin.isValue, Finsupp.sum_single_index]
    · simp

/-
a = Unit → r • X
b = Unit → T 0 + T 1
-/
example (f g : PowerSeries R) (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) := by
  simp only [IsExponential] at hf hg ⊢
  simp only [coe_subst (T 0).prop, coe_subst (T 1).prop, coe_subst (T 0 + T 1).prop] at hf hg ⊢
  simp only [map_mul, hf, hg]
  ring

noncomputable example : PowerSeries R := X
variable {r : R}

noncomputable example (r : R) : PowerSeries R := r • X
#check (r • T 0 : Dom 1 R)
#check fun (f : MvPowerSeries (Fin 1) R) ↦ subst (r • T 0 : Dom 1 R) f
noncomputable example (f : PowerSeries R) (hf : IsExponential f) (r : R) :
    IsExponential (subst (r • T 0 : Dom 1 R) f) := by
  simp only [IsExponential] at hf ⊢
  let hb := (T 0 + T 1 : Dom R).prop
  let ha := let h := MvPowerSeries.subst_comp_subst_apply (R := R)


/-
  R⟦X⟧ → R⟦X⟧ → R⟦T₀, T₁⟧
  X -> r • X, X -> T₀ + T₁
  f(X) → f(rX) → f(rX) (T₀+T₁) = f( r(T₀+t₁))

  f ∈ R⟦σ⟧, a : σ → R⟦τ⟧  gives f(a) ∈ R⟦τ⟧
  b : τ → C
  may compute f(a) (b)  = eval b f(a)  = eval b (eval a f)
  eval b may be used as ε : R ⟦τ⟧ → C, continuous
  f(a) (b) = ε (eval a f)
     = [comp_eval] eval (s ↦ ε (a s)) f
  But ε (a s) = eval b (a s)
    = eval (s ↦ eval b (a s)) f



-/
  sorry
end ExponentialPowerSeries
