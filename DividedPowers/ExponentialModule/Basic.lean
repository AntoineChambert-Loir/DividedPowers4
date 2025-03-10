/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Exponential module of a commutative ring

Let `R` be a commutative ring. The exponential module of `R` is the set of all power series
`f : R⟦X⟧` that are of exponential type : `f (X + Y) = f X * f Y` where `X` and `Y` are two
indeterminates. It is an abelian group under multiplication, and an `R`-module under rescaling.

## Main Definitions

* `PowerSeries.IsExponential` : for `f : R⟦X⟧`, `IsExponential f` says that `f` is of
  exponential type.

* `PowerSeries.ExponentialModule R` : the exponential module of the commutative ring `R`.

* `PowerSeries.ExponentialModule.linearMap`: for an `A`-algebra map `f : R →ₐ[A] S`, we define
  the induced `linearMap f : ExponentialModule R →ₗ[A] ExponentialModule S`.

## TODO - DONE

* Prove that the inverse of a power series of exponential type is exponential,
the inverse being given by `f (-X)`.

-/

section SMul

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommSemiring R]

@[simp]
lemma MvPolynomial.coe_smul (φ : MvPolynomial σ R) (r : R) :
  (r • φ : MvPolynomial σ R) = r • (φ : MvPowerSeries σ R) := rfl

@[simp]
lemma Polynomial.coe_smul (φ : Polynomial R) (r : R) :
  (r • φ : Polynomial R) = r • (φ : PowerSeries R) := rfl

end SMul



open Finset Finsupp MvPowerSeries Nat

variable {A R S : Type*} [CommRing A] [CommRing R] [Algebra A R] [CommRing S] [Algebra A S]

-- MI : why make this private?
open MvPolynomial in
/-- The formula for the `d`th coefficient of `(X 0 + X 1) ^ n`. -/
private lemma MvPolynomial.coeff_add_pow (d : Fin 2 →₀ ℕ) (n : ℕ) :
    coeff d ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) =
      if (d 0, d 1) ∈ antidiagonal n then n.choose (d 0) else 0 := by
  have hmon : ∀ (u v : ℕ), X (0 : Fin 2) ^ u * X 1 ^ v =
      monomial (single 0 u + single 1 v) (1 : R) := by
    intro u v
    rw [monomial_eq, prod_of_support_subset _ (subset_univ _) _ (fun i _ ↦ by rw [pow_zero])]
    simp only [Fin.isValue, ne_eq, Finsupp.coe_add, Pi.add_apply, Fin.prod_univ_two, single_eq_same,
      C_1, one_ne_zero, not_false_eq_true, single_eq_of_ne, add_zero, zero_ne_one, zero_add,
      one_mul]
  rw [Commute.add_pow' (Commute.all _ _), coeff_sum]
  simp only [nsmul_eq_smul, coeff_smul, Fin.isValue, cast_ite, cast_zero, hmon]
  split_ifs with hd
  · rw [sum_eq_single (d 0, d 1) _ (fun hd' ↦ absurd hd hd')]
    · rw [coeff_monomial, if_pos]
      · simp only [Fin.isValue, nsmul_eq_mul, mul_one]
      · ext i
        match i with
        | 0 => simp
        | 1 => simp
    · intro e _ hed
      rw [coeff_monomial, if_neg, smul_zero]
      intro hde
      apply hed
      simp [← hde]
  · refine sum_eq_zero (fun e he ↦ ?_)
    rw [coeff_monomial, if_neg, smul_zero]
    intro hed
    apply hd
    simpa [← hed, mem_antidiagonal] using he

namespace PowerSeries

section Bivariate

/-- Notation for the first variable of the bivariate power series ring `R⟦X₀, X₁⟧. -/
noncomputable abbrev X₀ {R : Type*} [Semiring R] := MvPowerSeries.X (σ := Fin 2) (R := R) 0

/-- Notation for the second variable of the bivariate power series ring `R⟦X₀, X₁⟧. -/
noncomputable abbrev X₁ {R : Type*} [Semiring R] := MvPowerSeries.X (σ := Fin 2) (R := R) 1

lemma coeff_subst_single {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff R e (subst (MvPowerSeries.X s) f) =
      if e = single s (e s) then PowerSeries.coeff R (e s) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.substDomain_of_constantCoeff_zero (by simp)),
    finsum_eq_single _ (e s)]
  · rw [MvPowerSeries.coeff_X_pow]
    simp only [Fin.isValue, ↓reduceIte, smul_eq_mul, mul_one]
    split_ifs with he
    · rw [mul_one]
    · rw [mul_zero]
  · intro d hd
    simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
    intro hd'
    simp only [hd', single_eq_same, ne_eq, not_true_eq_false] at hd

lemma forall_congr_curry {α : Type*} {p : (Fin 2 → α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 → α, p e ↔ q (e 0) (e 1)) :
    (∀ (e : Fin 2 → α), p e) ↔ ∀ (u v : α), q u v := by
  rw [Equiv.forall_congr_left (finTwoArrowEquiv α)]
  simp only [finTwoArrowEquiv_symm_apply, Prod.forall, hpq]
  rfl

lemma forall_congr_curry₀ {α : Type*} [Zero α] {p : (Fin 2 →₀ α) → Prop} {q : α → α → Prop}
    (hpq : ∀ e : Fin 2 →₀ α, p e ↔ q (e 0) (e 1)) :
    (∀ e, p e) ↔ ∀ u v, q u v := by
  rw [Equiv.forall_congr_left (equivFunOnFinite.trans (finTwoArrowEquiv α))]
  simp [finTwoArrowEquiv_symm_apply, Prod.forall, hpq]

lemma coeff_subst_add_X₀_X₁ (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff R e) (subst (X₀ + X₁) f) =
      (e 0 + e 1).choose (e 0) * coeff R (e 0 + e 1) f := by
  rw [PowerSeries.subst, MvPowerSeries.coeff_subst
    (MvPowerSeries.substDomain_of_constantCoeff_zero (fun _ ↦ by simp))]
  simp only [Fin.isValue, Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul]
  simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
    MvPolynomial.coeff_coe]
  rw [finsum_eq_single _ (single () (e 0 + e 1)), mul_comm]
  · apply congr_arg₂
    simp only [Fin.isValue, single_add, Finsupp.coe_add, Pi.add_apply, single_eq_same,
      MvPolynomial.coeff_add_pow e _, mem_antidiagonal, ↓reduceIte]
    simp [coeff]
  · intro d hd'
    simp [MvPolynomial.coeff_add_pow]
    intro hd
    exfalso
    apply hd'
    ext
    simp only [PUnit.default_eq_unit, hd, single_eq_same]


lemma coeff_subst_mul_X₀_X₁ (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff R e (subst X₀ f * subst X₁ f) = coeff R (e 0) f * coeff R (e 1) f := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (single 0 (e 0), single 1 (e 1))]
  · apply congr_arg₂ <;>
    · simp only [coeff_subst_single, single_eq_same, if_pos]
  · intro b hb hb'
    rw [mem_antidiagonal] at hb
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← hb, h0.1, h1.1]
    simp
  · intro he
    exfalso
    apply he
    simp only [mem_antidiagonal]
    ext i
    match i with
    | 0 => simp
    | 1 => simp

end Bivariate

/-- A power series `f : R⟦X⟧` is exponential if `f(X + Y) = f(X)*f(Y)` and `f(0) = 1`. -/
structure IsExponential (f : R⟦X⟧) : Prop where
  add_mul : subst (S := R) (X₀ + X₁) f = subst X₀ f * subst X₁ f
  constantCoeff : constantCoeff R f = 1

/-- A power series `f` satisfies `f(X + Y) = f(X)*f(Y)` iff its coefficients `f n` satisfy
  the relations `(p + q).choose p * f (p + q)= f p * f q`. -/
theorem subst_add_eq_mul_iff (f : R⟦X⟧) :
    (subst (S := R) (X₀ + X₁) f) = (subst X₀ f) * (subst X₁ f) ↔
      ∀ (p q : ℕ), (p + q).choose p * (coeff R (p + q) f) = coeff R p f * coeff R q f := by
  rw [MvPowerSeries.ext_iff]
  exact forall_congr_curry₀ (fun e ↦ by rw [coeff_subst_add_X₀_X₁ , coeff_subst_mul_X₀_X₁])

/-- A power series `f` is exponential iff its coefficients `f n` satisfy the relations
  `(p + q).choose p * f (p + q)= f p * f q` and its constant coefficient is `1`. -/
theorem isExponential_iff {f : R⟦X⟧} :
    IsExponential f ↔ (∀ p q, (p + q).choose p * coeff R (p + q) f = coeff R p f * coeff R q f) ∧
      (constantCoeff R f = 1) := by
  rw [← subst_add_eq_mul_iff]
  exact ⟨fun hf ↦ ⟨hf.add_mul, hf.constantCoeff⟩, fun hf ↦ ⟨hf.1, hf.2⟩⟩

namespace IsExponential

/-- The unit power series is exponential -/
protected theorem one : IsExponential (1 : R⟦X⟧) where
  add_mul := by
    rw [← Polynomial.coe_one, subst_coe (substDomain_of_constantCoeff_zero (by simp)),
      subst_coe (substDomain_of_constantCoeff_zero (by simp)),
      subst_coe (substDomain_of_constantCoeff_zero (by simp))]
    simp only [map_one, mul_one]
  constantCoeff := by simp only [map_one]

/-- If `f` and `g` are exponential, then so is `f * g`. -/
protected theorem mul {f g : PowerSeries R} (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) where
  add_mul := by
    repeat rw [← coe_substAlgHom (substDomain_of_constantCoeff_zero (by simp))]
    simp only [map_mul, coe_substAlgHom, hf.add_mul, hg.add_mul]
    ring
  constantCoeff := by simp only [map_mul, hf.constantCoeff, hg.constantCoeff, mul_one]

/-- If `f` is exponential and  `n : ℕ`, then `f ^ n` is exponential. -/
protected theorem npow {f : R⟦X⟧} (hf : IsExponential f) (n : ℕ) :
    IsExponential (f ^ n) := by
  induction n with
  | zero => simp only [zero_eq, pow_zero, IsExponential.one]
  | succ n hn => simp only [pow_succ, hn.mul hf]

/-- If `f` is exponential, then `f(r • T)` is exponential, for any `r : R`. -/
protected theorem rescale (a : A) {f : PowerSeries R} (hf : IsExponential f) :
    IsExponential (rescale (algebraMap A R a) f) where
  constantCoeff := by
    rw [← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp only [pow_zero, coeff_zero_eq_constantCoeff, one_smul, hf.constantCoeff]
    simp only [mul_one]
  add_mul := by
    repeat rw [subst_linear_subst_scalar_comm]
    simp only [← MvPowerSeries.coe_rescale_algHom, ← map_mul, hf.add_mul]
    -- We prove the hypothesis of the last two applications of `subst_linear_subst_scalar_comm`.
    repeat
      intro d hd
      simp only [Fin.isValue, map_add, MvPowerSeries.coeff_X]
      rw [if_neg]
      intro hd'
      apply hd
      rw [hd']
      simp only [Fin.isValue, sum_single_index]
    -- The first application of `subst_linear_subst_scalar_comm` is a bit different.
    · intro d hd
      simp only [Fin.isValue, map_add, MvPowerSeries.coeff_X]
      split_ifs with h0 h1 h1
      · rw [h1, single_left_inj (by norm_num)] at h0
        exfalso; exact one_ne_zero h0
      · exfalso; apply hd
        simp only [h0, Fin.isValue, sum_single_index]
      · exfalso; apply hd
        simp only [h1, Fin.isValue, sum_single_index]
      · simp only [add_zero]

protected theorem rescale_add (r s : A) {f : R⟦X⟧} (hf : IsExponential f) :
    rescale (algebraMap A R r + algebraMap A R s) f =
      rescale (algebraMap A R r) f * rescale (algebraMap A R s) f := by
  let a : Fin 2 → PowerSeries R
  | 0 => (algebraMap A R r) • X
  | 1 => (algebraMap A R s) • X
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
  simp only [PowerSeries.subst, ← MvPowerSeries.coe_substAlgHom ha] at hf'
  repeat rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.substDomain_of_constantCoeff_zero
    (by simp))] at hf'
  simp only [MvPowerSeries.substAlgHom_comp_substAlgHom_apply, map_mul] at hf'
  simp only [MvPowerSeries.coe_substAlgHom] at hf'
  simp only [rescale_eq_subst, subst]
  convert hf' <;>
  simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_add,
      MvPowerSeries.subst_coe ha] <;>
  simp only [Fin.isValue, map_add, MvPolynomial.aeval_X, add_smul, a, algebraMap_smul, Fin.isValue]

protected theorem neg {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (rescale  (-1 : R) f) := hf.rescale (-1 : R)

protected theorem self_mul_neg_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    f * (rescale (-1 : R) f) = 1 := by
  have hadd := hf.rescale_add (1 : R) (-1 : R)
  simp only [Algebra.id.map_eq_id, RingHom.id_apply, add_neg_cancel, rescale_zero,
    RingHom.coe_comp, Function.comp_apply, rescale_one] at hadd
  rw [← hadd, hf.constantCoeff, map_one]

protected theorem neg_mul_self_eq_one {f : R⟦X⟧} (hf : IsExponential f) :
    (rescale (-1) f) * f = 1 := by rw [mul_comm, hf.self_mul_neg_eq_one]

protected theorem isUnit {f : R⟦X⟧} (hf : IsExponential f) : IsUnit f :=
  isUnit_iff_exists_inv'.mpr ⟨(rescale (-1) f),  hf.neg_mul_self_eq_one⟩

protected theorem inverse_eq_neg_mul_self {f : R⟦X⟧} (hf : IsExponential f) :
    Ring.inverse f = (rescale (-1) f) := by
  rw [Ring.inverse, dif_pos hf.isUnit]
  exact hf.isUnit.unit.inv_eq_of_mul_eq_one_left hf.neg_mul_self_eq_one

protected theorem invOfUnit_eq_rescale_neg_one {f : R⟦X⟧} (hf : IsExponential f) :
    (f.invOfUnit 1) = rescale (-1) f := by
  rw [← IsUnit.mul_right_inj hf.isUnit]
  rw [f.mul_invOfUnit, hf.self_mul_neg_eq_one]
  simp only [Units.val_one, hf.constantCoeff]

protected theorem inv {f : R⟦X⟧} (hf : IsExponential f) : IsExponential (f.invOfUnit 1) := by
  simp [hf.invOfUnit_eq_rescale_neg_one, hf.neg]

protected theorem map (φ : R →+* S) {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (PowerSeries.map φ f) := by
  rw [isExponential_iff]
  constructor
  · intro p q
    simp only [coeff_map, ← map_mul, ← (isExponential_iff.mp hf).1 p q]
    simp only [map_mul, map_natCast]
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff, hf.constantCoeff, map_one]

end IsExponential

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

open Additive

section Instances

noncomputable instance : SMul A (Additive R⟦X⟧) where
  smul r f := ofMul.toFun (rescale (algebraMap A R r) (toMul f))

lemma toAdditive_smul_coe (r : A) (f : R⟦X⟧) :
  r • (ofMul f) = ofMul (rescale (algebraMap A R r) f) := rfl

lemma toAdditive_smul_coe' (r : A) (f : Additive R⟦X⟧) :
  toMul (r • f) = rescale (algebraMap A R r) (toMul f) := rfl

noncomputable instance : DistribMulAction A (Additive R⟦X⟧) where
  one_smul := by
    simp only [Additive.forall, toAdditive_smul_coe, map_one, rescale_one, RingHom.id_apply,
      implies_true]
  mul_smul := by
    simp only [Additive.forall, toAdditive_smul_coe, map_mul, ← rescale_rescale_apply, implies_true]
  smul_zero a := by
    rw [← ofMul_one, toAdditive_smul_coe, ← coe_rescale_algHom, map_one]
  smul_add := by
    simp only [Additive.forall, toAdditive_smul_coe, ← ofMul_mul,
      ← coe_rescale_algHom, map_mul, forall_const]

end Instances


variable (R) in
/-- The `R`-module of exponential power series `f : R⟦X⟧` satisfying `f(X+Y) = f(X) f(Y)` and
  `f(0) = 1`. The addition law is the multiplication of power series.
  The scalar multiplication law is given by `PowerSeries.rescale`.
  This is implemented as an `AddSubmonoid (Additive R⟦X⟧) `. -/
def ExponentialModule : AddSubmonoid (Additive R⟦X⟧) where
  carrier := { f : Additive (R⟦X⟧) | IsExponential (toMul f) }
  add_mem' {f g} hf hg := by simp only [Set.mem_setOf_eq, toMul_add, hf.mul hg]
  zero_mem' := by simp only [Set.mem_setOf_eq, toMul_zero, IsExponential.one]

lemma mem_exponentialModule_iff (f : R⟦X⟧) :
    ofMul f ∈ ExponentialModule R ↔ IsExponential f := by
  simp only [ExponentialModule, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    toMul_ofMul]

lemma mem_exponentialModule_iff' (f : Additive R⟦X⟧) :
    f ∈ ExponentialModule R ↔ IsExponential (toMul f) := by
  simp only [ExponentialModule, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

namespace ExponentialModule

open PowerSeries Additive

/-- The coercion map from `ExponentialModule R` to `R⟦X⟧`. -/
@[coe] def toPowerSeries (f : ExponentialModule R) : R⟦X⟧ := toMul (f : Additive R⟦X⟧)

variable (R) in
instance instCoe : Coe (ExponentialModule R) R⟦X⟧ := ⟨toPowerSeries⟩

lemma coe_injective : Function.Injective ((↑) : ExponentialModule R → R⟦X⟧) :=
  fun f g ↦ by
    simp only [toPowerSeries, EmbeddingLike.apply_eq_iff_eq, SetLike.coe_eq_coe, imp_self]

@[simp, norm_cast]
lemma coe_inj {f g : ExponentialModule R} : (f : R⟦X⟧) = ↑g ↔ f = g := coe_injective.eq_iff

@[ext]
lemma coe_ext {f g : ExponentialModule R} (h : (f : R⟦X⟧) = ↑g) : f = g := coe_injective h

@[simp]
theorem toMul_val_eq_coe {f : ExponentialModule R} : toMul (↑f : Additive R⟦X⟧) = ↑f := rfl

noncomputable instance instSMul : SMul A (ExponentialModule R) where
  smul r f := ⟨r • (f : Additive R⟦X⟧), by
    simp only [mem_exponentialModule_iff', toAdditive_smul_coe',f.prop.rescale (algebraMap A R r)]
    exact f.prop.rescale (algebraMap A R r)⟩

theorem smul_def (r : A) (f : ExponentialModule R) :
  (r • f : ExponentialModule R) = r • (f : Additive R⟦X⟧) := rfl

noncomputable instance instModule : Module A (ExponentialModule R) where
  one_smul f := by rw [← Subtype.coe_inj, smul_def, one_smul]
  mul_smul r s f := by simp only [← Subtype.coe_inj, smul_def, mul_smul]
  smul_zero r := by rw [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero, smul_zero]
  smul_add r f g := by
    simp only [← Subtype.coe_inj, smul_def, AddSubmonoid.coe_add, smul_add]
  add_smul r s f := by
    simp only [← Subtype.coe_inj, smul_def, AddSubmonoid.coe_add]
    apply Additive.toMul.injective
    simp only [toAdditive_smul_coe', toMul_add, map_add, f.prop.rescale_add r s ]
  zero_smul f := by
    simp only [← Subtype.coe_inj, smul_def, ZeroMemClass.coe_zero]
    apply Additive.toMul.injective
    have hf : constantCoeff R f = 1 := f.prop.constantCoeff
    simp only [toAdditive_smul_coe', map_zero, rescale_zero, toMul_val_eq_coe, RingHom.coe_comp,
      Function.comp_apply, hf, map_one, toMul_zero]

-- TODO: continue from here.

lemma coe_add (f g : ExponentialModule R) : (↑(f + g) : R⟦X⟧) = ↑f * ↑g := by
  simp only [toPowerSeries, AddSubmonoid.coe_add, toMul_add]

lemma coe_smul (r : A) (f : ExponentialModule R) :
    ((r • f) : ExponentialModule R) = rescale (algebraMap A R r) (f : R⟦X⟧) :=
  rfl

noncomputable instance : AddCommGroup (ExponentialModule R) where
  neg f := (-1 : ℤ) • f
  zsmul n f := n • f
  zsmul_zero' f := by simp [← Subtype.coe_inj]
  zsmul_succ' n f := by
    simp only [succ_eq_add_one, Int.ofNat_eq_coe, cast_add, cast_one, ← Subtype.coe_inj,
      AddSubmonoid.coe_add, add_smul, one_smul, AddSubmonoid.coe_add]
  zsmul_neg' n f := by
    dsimp only
    rw [Int.negSucc_eq]
    rw [← smul_assoc]
    simp
  neg_add_cancel f := by
    rw [← Subtype.coe_inj]
    apply Additive.toMul.injective
    simp only [toPowerSeries, AddSubmonoid.coe_add, toMul_add]
    convert isExponential_neg_mul_self_eq_one f.2 using 2
    simp [coe_smul]
  add_comm f g := add_comm f g

instance instIsScalarTower
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (ExponentialModule A) where
  smul_assoc r s f := by
    apply coe_injective
    simp only [coe_smul]
    rw [← algebraMap_smul S, smul_eq_mul, map_mul, ← rescale_rescale_apply]
    apply congr_fun
    ext f n
    simp only [coeff_rescale, ← map_pow, algebraMap_smul, map_pow]
    simp only [IsScalarTower.algebraMap_eq R S A, RingHom.coe_comp, Function.comp_apply]


lemma coe_ofMul (f : R⟦X⟧) (hf : IsExponential f) :
    ↑(⟨ofMul f, hf⟩ : ExponentialModule R) = f := rfl

lemma isExponential_coe (f : ExponentialModule R) :
    IsExponential (f : R⟦X⟧) := f.prop

lemma constantCoeff_coe (f : ExponentialModule R) :
    constantCoeff R (f : R⟦X⟧) = 1 := f.prop.constantCoeff

lemma add_mul_coe (f : ExponentialModule R) :
    subst (S := R) (X₀ + X₁) (f : R⟦X⟧) = (subst X₀ (f : R⟦X⟧)) * (subst X₁ (f : R⟦X⟧)) :=
  f.prop.add_mul

lemma add_mul_coe' (f : ExponentialModule R) (p q : ℕ) :
    (p + q).choose p * (coeff R (p + q) (f : R⟦X⟧)) = coeff R p f * coeff R q f :=
  (subst_add_eq_mul_iff (R := R) f).mp (add_mul_coe f) p q

variable {S : Type*} [CommRing S] [Algebra A S] (φ : R →ₐ[A] S)

/-- Given `A`-algebras `R` and `S`, this is the linear map between multivariate formal
power series induced by an `A`-algebra map on the coefficients.-/
def linearMap : ExponentialModule R →ₗ[A] ExponentialModule S where
  toFun := fun f ↦
    ⟨ofMul (PowerSeries.map φ (f : R⟦X⟧)), by
      simp [mem_exponentialModule_iff]
      exact isExponential_map (φ  : R →+* S) f.prop⟩
  map_add' := fun f g ↦ by
    apply coe_injective
    simp only [coe_add, map_mul, ofMul_mul]
    rfl
  map_smul' := fun a f ↦ by
    apply coe_injective
    simp only [coe_smul, RingHom.id_apply, coe_ofMul]
    rw [rescale_map_eq_map_rescale]

theorem coeff_linearMap (n : ℕ) (f : ExponentialModule R) :
    coeff S n (linearMap φ f) = φ (coeff R n f) := rfl

theorem coeff_neg_X_pow (n d : ℕ) :
    (coeff R n) ((-X) ^ d) = if n = d then (if Even n then 1 else -1) else 0 := by
  have : -X = (C R (-(1 : R))) * X := by simp only [map_neg, map_one, neg_mul, one_mul]
  have heq : ∑ p ∈ antidiagonal n, (coeff R p.1) ((C R) (-1) ^ d) * (coeff R p.2) (X ^ d) =
      (coeff R 0) ((C R) (-1) ^ d) * (coeff R n) (X ^ d) := by
    rw [Finset.sum_eq_single (0, n)]
    · intro p hpin hpne
      have hp1 : p.1 ≠ 0 := by
        intro h
        rw [mem_antidiagonal, h, zero_add] at hpin
        apply hpne
        ext
        exacts [h, hpin]
      have hC : ((C R) (-1) ^ d) = (C R ((-1) ^d)) := by simp only [map_neg, map_one, map_pow]
      rw [hC, coeff_C, if_neg hp1, zero_mul]
    · intro hnin
      have hin : (0, n) ∈ antidiagonal n  :=  by simp only [mem_antidiagonal, zero_add]
      exact absurd hin hnin
  rw [this, mul_pow, coeff_mul, heq]
  simp only [map_neg, map_one, coeff_zero_eq_constantCoeff, map_pow, constantCoeff_one]
  rw [coeff_X_pow]
  split_ifs with hd hn
  · rw [← hd, mul_one, neg_one_pow_eq_pow_mod_two, even_iff.mp hn, pow_zero]
  · rw [← hd, mul_one, neg_one_pow_eq_pow_mod_two, not_even_iff.mp hn, pow_one]
  · rw [mul_zero]

lemma substDomain_neg_X : SubstDomain (S := R) (-X) := by
  have hcoeff' : (MvPowerSeries.constantCoeff Unit R) (-X) =
      (PowerSeries.constantCoeff R) (-X) := by rw [constantCoeff]
  exact substDomain_of_constantCoeff_zero (by simp [hcoeff', constantCoeff_X])

open MvPowerSeries.WithPiTopology in
lemma coeff_subst_neg_X (f : R⟦X⟧) (n : ℕ) :
    (coeff R n) (subst (-X) f) = if Even n then (coeff R n) f else - ((coeff R n) f ) := by
  letI : UniformSpace R := ⊥
  erw [subst, coeff_subst substDomain_neg_X]
  have hcoeff : ∀ (d : ℕ), (MvPowerSeries.coeff R (single () n)) ((-X) ^ d) =
    (PowerSeries.coeff R n) ((-X) ^ d) := fun d ↦ by rw [coeff]
  have hn : ∀ (d : ℕ), d ≠ n →
      (coeff R d) f • (MvPowerSeries.coeff R (single () n)) ((-X) ^ d) = 0 := by
    intro d hd
    rw [hcoeff, coeff_neg_X_pow, if_neg hd.symm, smul_zero]
  erw [finsum_eq_single _ _ hn, coeff_neg_X_pow n n, smul_eq_mul]
  split_ifs with hn
  · rw [mul_one]
  · ring
  · exact absurd rfl hn
  · exact absurd rfl hn

lemma isExponential_inv {f : R⟦X⟧} (hf : IsExponential f) :
    IsExponential (f.subst (-PowerSeries.X (R := R))) := by
  simp only [isExponential_iff] at hf ⊢
  have hf1 := hf.1
  have hf2 := hf.2
  constructor
  · intros m n
    specialize hf1 m n
    simp [coeff_subst_neg_X]
    split_ifs with h
    · exact hf1
    · exfalso; rw [even_add] at h;  tauto
    · exfalso; rw [even_add] at h;  tauto
    · rw [neg_neg, hf1]
    · exfalso; rw [even_add] at h;  tauto
    · rw [hf1]
    · rw [hf1]
    · exfalso; rw [even_add] at h;  tauto
  · rw [constantCoeff, constantCoeff_subst substDomain_neg_X]
    have hC : (MvPowerSeries.constantCoeff Unit R) X =
      PowerSeries.constantCoeff R PowerSeries.X := by rw [constantCoeff]
    have h0 : ∀ (d : ℕ), d ≠ 0 →
        (coeff R d) f • (MvPowerSeries.constantCoeff Unit R) ((-X) ^ d) = 0 := by
      intros d hd
      rw [map_pow, map_neg, hC, PowerSeries.constantCoeff_X]
      simp [neg_zero, zero_pow hd, smul_eq_mul, mul_zero]
    rw [finsum_eq_single _ _ h0]
    simp only [coeff_zero_eq_constantCoeff, hf2, pow_zero, MvPowerSeries.constantCoeff_one,
      smul_eq_mul, mul_one]


end ExponentialModule

end PowerSeries
