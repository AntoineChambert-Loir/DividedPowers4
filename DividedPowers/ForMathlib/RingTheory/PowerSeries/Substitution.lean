/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/

import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Substitution
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

/-- Families of power series which can be substituted. -/
structure HasSubst (a : MvPowerSeries τ S) : Prop where
  const_coeff : IsNilpotent (MvPowerSeries.constantCoeff τ S a)

theorem hasSubst_of_constantCoeff_nilpotent {a : MvPowerSeries τ S}
    (ha : IsNilpotent (MvPowerSeries.constantCoeff τ S a)) : HasSubst a where
  const_coeff := ha

theorem hasSubst_iff (a : MvPowerSeries τ S) :
    HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
    (Function.const Unit ha.const_coeff),
   fun ha  ↦ hasSubst_of_constantCoeff_nilpotent (ha.const_coeff ())⟩

theorem hasSubst_of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) : HasSubst a where
  const_coeff := by simp only [ha, IsNilpotent.zero]

theorem hasSubst_X : HasSubst (X : R⟦X⟧) :=
  hasSubst_of_constantCoeff_zero (by
    change constantCoeff R X = 0
    rw [constantCoeff_X])

theorem hasSubst_smul_X (a : A) : HasSubst (a • X : R⟦X⟧) :=
  hasSubst_of_constantCoeff_zero (by
    change constantCoeff R (a • X) = 0
    rw [← coeff_zero_eq_constantCoeff]
    simp [LinearMap.map_smul_of_tower, coeff_zero_X, smul_zero])

variable {υ T : Type*} [CommRing T] [Algebra R T] [Algebra S T]

/-- Substitution of power series into a power series -/
noncomputable def subst [Algebra R S] (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S}

theorem HasSubst.const (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun (_ : Unit) ↦ a) where
  const_coeff  := fun _ ↦ ha.const_coeff
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom [Algebra R S] (ha : HasSubst a) :
    PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_substAlgHom [Algebra R S] (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

theorem subst_add [Algebra R S] (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_pow [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_mul [Algebra R S] (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_smul [Algebra A S] [Algebra R S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem coeff_subst_finite [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : ℕ) ↦ (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))).support := by
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    ⇑(Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext d
  simp only [Finsupp.prod_pow, Finset.univ_unique, PUnit.default_eq_unit, Finset.prod_singleton,
    LinearEquiv.coe_toEquiv_symm, EquivLike.coe_coe, Function.comp_apply,
    Finsupp.LinearEquiv.finsuppUnique_symm_apply, Finsupp.single_eq_same]
  congr

theorem coeff_subst [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff S e (subst a f) =
      finsum (fun (d : ℕ) ↦
        (coeff R d f) • (MvPowerSeries.coeff S e (a ^ d))) := by
  erw [MvPowerSeries.coeff_subst ha.const f e]
  rw [← finsum_comp_equiv (Finsupp.LinearEquiv.finsuppUnique ℕ ℕ Unit).toEquiv.symm]
  apply finsum_congr
  intro d
  congr
  · ext; simp
  · simp

theorem constantCoeff_subst [Algebra R S] (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (MvPowerSeries.constantCoeff τ S (a ^ d))) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X [Algebra R S] (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f

theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) :
    (p : PowerSeries R) =
      ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) := by
  change (Polynomial.coeToPowerSeries.algHom R) p =
    (MvPolynomial.coeToMvPowerSeries.algHom R)
      (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R) p)
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.id.map_eq_id, Polynomial.coe_X,
    map_X]
  erw [AlgHom.comp_apply]
  simp [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply, PowerSeries.X,
    Algebra.id.map_eq_id, MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]

theorem substAlgHom_coe [Algebra R S] (ha : HasSubst a) (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries, substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_coe ha.const, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]

theorem substAlgHom_X [Algebra R S] (ha : HasSubst a) :
    substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, substAlgHom_coe, Polynomial.aeval_X]

theorem subst_coe [Algebra R S] (ha : HasSubst a) (p : Polynomial R) :
    subst (R := R) a (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X [Algebra R S] (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by rw [← coe_substAlgHom ha, substAlgHom_X]

theorem HasSubst.comp {a : PowerSeries S} (ha : HasSubst a)
    {b : MvPowerSeries υ T} (hb : HasSubst b):
    HasSubst (substAlgHom hb a) where
  const_coeff := MvPowerSeries.IsNilpotent_subst hb.const (ha.const_coeff)

variable {T : Type*} [CommRing T] [Algebra R T] {a : PowerSeries S} {b : MvPowerSeries υ T}
    {a' : MvPowerSeries τ S} {b' : τ → MvPowerSeries υ T}

theorem substAlgHom_comp_substAlgHom [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha)
      = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom  ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa only [funext_iff, DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
    Function.comp_apply, coe_substAlgHom]
    using substAlgHom_comp_substAlgHom (R := R) ha hb

theorem subst_comp_subst_apply [Algebra R S] [Algebra S T] [IsScalarTower R S T]
    (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

lemma rescale_eq_rescale (r : R) (f : PowerSeries R) :
    rescale r f = MvPowerSeries.rescale (fun _ ↦ r) f := by
  ext n
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp only [pow_zero, Finsupp.prod_single_index, smul_eq_mul]

lemma rescale_eq_subst (r : R) (f : PowerSeries R) :
    PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f := by
  rw [rescale_eq_rescale, MvPowerSeries.rescale_eq_subst, X, subst, Pi.smul_def']

/-- Rescale power series, as an `AlgHom` -/
noncomputable def rescaleAlgHom (r : R) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.rescaleAlgHom R (fun _ ↦ r)

lemma rescaleAlgHom_eq_rescaleAlgHom (r : R) (f : PowerSeries R) :
    rescaleAlgHom r f = MvPowerSeries.rescaleAlgHom _ (fun _ ↦ r) f := by
  simp only [rescaleAlgHom]

theorem coe_rescaleAlgHom (r : R) :
    (rescaleAlgHom r) = rescale r := by
  ext f
  rw [rescale_eq_rescale, RingHom.coe_coe, rescaleAlgHom_eq_rescaleAlgHom,
    MvPowerSeries.coe_rescaleAlgHom]

theorem rescaleAlgHom_comp (a b : A) :
    (rescaleAlgHom a).comp (rescaleAlgHom b) = rescaleAlgHom (a * b) := by
  simp only [rescaleAlgHom, MvPowerSeries.rescaleAlgHom_comp]; rfl

theorem rescale_rescale_apply (a b : R) (f : R⟦X⟧) :
    (f.rescale b).rescale a = f.rescale (a * b) := by
  simp only [rescale_eq_rescale]
  exact MvPowerSeries.rescale_rescale_apply _ _ f

/-- When `p` is linear, substitution of `p` and then a scalar homothety is substitution of
  the homothety then `p`. -/
lemma subst_linear_subst_scalar_comm (a : R) {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d p = 0)
    (f : PowerSeries R) :
    subst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply hasSubst_of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    apply hp_lin
    simp only [Finsupp.sum_zero_index, ne_eq, zero_ne_one, not_false_eq_true]
  rw [rescale_eq_subst, MvPowerSeries.rescale_eq_subst, subst_comp_subst_apply (hasSubst_smul_X _) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.hasSubst_rescale R _),
    funext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X,
    ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_linear_eq_smul _ _ hp_lin, subst]

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
