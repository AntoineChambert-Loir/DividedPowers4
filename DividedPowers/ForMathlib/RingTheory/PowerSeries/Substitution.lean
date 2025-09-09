/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Substitutions in univariate power series

Here we specialize the results of `DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Substitution`
to the case of univariate power series.


We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Let `τ`, `R`, `S` be types, with `CommRing R`, `CommRing S`, and `Algebra R S`.

We endow `PowerSeries R` and `MvPowerSeries τ S` with the product topology induced by the
discrete topology on the coefficient rings.

Given `a : MvPowerSeries τ S` and `f : PowerSeries R`, `f.subst a : MvPowerSeries τ S`
is the power series obtained by substituting the indeterminate of `f` by `a`.
It is defined as a special case of `MvPowerSeries.subst`. Its values are irrelevant unless the
constant coefficient of `a` is nilpotent.

We also expand the API for the definition `PowerSeries.rescale`, following the multivariate case.

## Main definitions

* `PowerSeries.subst`: substitution of a multivariate power series into a univariate power series.
* `PowerSeries.substAlgHom`: substitution of a multivariate power series into a univariate power
  series, as an algebra morphism.

## Main results

* `MvPowerSeries.continuous_subst`: continuity of the substitution.
* `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent` : if `σ` is finite, then the nilpotency
  condition is enough for `HasSubst`.
* `MvPowerSeries.hasSubst_of_constantCoeff_zero` : if `σ` is finite, then having zero constant
  coefficient is enough for `HasSubst`.

-/

namespace PowerSeries

variable {A R τ S: Type*} [CommRing A] [CommRing R] [Algebra A R] [CommRing S]

open MvPowerSeries.WithPiTopology

lemma rescale_eq_rescale (r : R) (f : PowerSeries R) :
    rescale r f = MvPowerSeries.rescale (fun _ ↦ r) f := by
  ext n
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp

lemma rescale_eq_subst (r : R) (f : PowerSeries R) :
    PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f := by
  rw [rescale_eq_rescale, MvPowerSeries.rescale_eq_subst, X, subst, Pi.smul_def']

/-- Rescale power series, as an `AlgHom` -/
noncomputable def rescaleAlgHom (r : R) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.rescaleAlgHom (fun _ ↦ r)

lemma rescaleAlgHom_eq_rescaleAlgHom (r : R) (f : PowerSeries R) :
    rescaleAlgHom r f = MvPowerSeries.rescaleAlgHom (fun _ ↦ r) f := by
  simp only [rescaleAlgHom]

theorem rescaleAlgHom_apply (r : R) : (rescaleAlgHom r) = rescale r := by
  ext f
  rw [rescale_eq_rescale, RingHom.coe_coe, rescaleAlgHom_eq_rescaleAlgHom,
    MvPowerSeries.rescaleAlgHom_apply]

theorem rescaleAlgHom_mul (a b : A) :
    rescaleAlgHom (a * b) = (rescaleAlgHom b).comp (rescaleAlgHom a)  := by
  simp only [rescaleAlgHom, ← MvPowerSeries.rescaleAlgHom_mul]; rfl

theorem rescale_mul' (a b : R) (f : R⟦X⟧) :
    f.rescale (a * b) = (f.rescale a).rescale b  := by
  simp only [rescale_eq_rescale]
  rw [← Pi.mul_def, MvPowerSeries.rescale_mul]
  simp

/-- When `p` is linear, substitution of `p` and then a scalar homothety is substitution of
  the homothety then `p`. -/
lemma subst_linear_subst_scalar_comm (a : R) {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff d p = 0)
    (f : PowerSeries R) :
    subst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply HasSubst.of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply hp_lin
    simp only [Finsupp.sum_zero_index, ne_eq, zero_ne_one, not_false_eq_true]
  rw [rescale_eq_subst, MvPowerSeries.rescale_eq_subst, subst_comp_subst_apply
    (HasSubst.smul_X' a) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.HasSubst.smul_X _),
    funext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X,
    ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_homogeneous_eq_smul (n := 1), subst,
    pow_one]
  intro d hd
  by_contra hd1
  exact hd (hp_lin d hd1)

theorem rescale_map_eq_map_rescale' (φ : R →+* S) (r : R) (f : R⟦X⟧) :
    rescale (φ r) (PowerSeries.map φ f) =
      PowerSeries.map (φ : R →+* S) (rescale r f) := by
  ext n
  simp [coeff_rescale, coeff_map, map_mul, map_pow]

theorem rescale_map_eq_map_rescale [Algebra A S] (φ : R →ₐ[A] S) (a : A) (f : R⟦X⟧) :
    rescale (algebraMap A S a) (PowerSeries.map φ f) =
      PowerSeries.map (φ : R →+* S) (rescale (algebraMap A R a) f) := by
  rw [← rescale_map_eq_map_rescale', RingHom.coe_coe, AlgHom.commutes]

end PowerSeries
