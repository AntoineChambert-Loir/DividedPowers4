/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Substitutions in multivariate power series

Here we define the substitution of multivariate power series into other multivariate power series.
We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Let `σ`, `τ`, `R`, `S` be types, with `CommRing R`, `CommRing S`, and `Algebra R S`.

We endow `MvPowerSeries σ R` and `MvPowerSeries τ S` with the product topology induced by the
discrete topology on the coefficient rings.

Given `a : σ → MvPowerSeries τ S` and `f : MvPowerSeries σ R`, `f.subst a : MvPowerSeries τ S`
is the power series obtained by substituting the indeterminates of `f` by the values given by `a`.
It is defined as a special case of `MvPowerSeries.eval₂`. Its values are irrelevant unless `a`
satisfies two conditions bundled in `HasSubst (a : σ → MvPowerSeries τ S)` :
  - for all `s : σ`, `constantCoeff τ S (a s)` is nilpotent.
  - when `a s` tends to zero for the filter of cofinite subsets of `σ`.

We also provide the definition `MvPowerSeries.rescale` that, given `a : σ → R` and
`f : MvPowerSeries σ R`, returns the power series obtained by substituting `a • X` into `f`. We
provide a comprehensive API for this definition.

## Main definitions

* `MvPowerSeries.subst`: substitution of multivariate power series into a multivariate power series.
* `MvPowerSeries.substAlgHom`: substitution of multivariate power series into a multivariate power
  series, as an algebra morphism.
* `MvPowerSeries.rescale` : given `a : σ → R` and `f : MvPowerSeries σ R`, this is the power series
  obtained by substituting `a • X` into `f`.

## Main results

* `MvPowerSeries.continuous_subst`: continuity of the substitution.
* `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent` : if `σ` is finite, then the nilpotency
  condition is enough for `HasSubst`.
* `MvPowerSeries.hasSubst_of_constantCoeff_zero` : if `σ` is finite, then having zero constant
  coefficient is enough for `HasSubst`.

-/

theorem Set.Finite.support_of_summable {α : Type*} [AddCommGroup α] [TopologicalSpace α]
    [DiscreteTopology α] {β : Type*} (f : β → α) (h : Summable f) : Set.Finite f.support := by
  classical
  obtain ⟨a, ha⟩ := h
  simp only [HasSum] at ha
  simp_rw [tendsto_atTop_nhds] at ha
  obtain ⟨s, hs⟩ := ha {a} rfl (isOpen_discrete _)
  apply Set.Finite.subset s.finite_toSet
  intro b
  rw [Function.mem_support, not_imp_comm]
  intro hb
  let hs' := hs (insert b s) (s.subset_insert b)
  simp only [Set.mem_singleton_iff] at hs hs'
  simpa [Finset.sum_insert hb, hs, add_eq_right] using hs'

theorem IsNilpotent.finsum {α : Type*} [CommSemiring α] {β : Type*} {f : β → α}
    (hf : ∀ b, IsNilpotent (f b)) : IsNilpotent (finsum f) := by
  classical
  by_cases h : Set.Finite f.support
  · rw [finsum_def, dif_pos h]
    exact Commute.isNilpotent_sum (fun b _ ↦ hf b) (fun i j hi hj ↦ Commute.all _ _)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]

section Semiring

variable {σ R S T : Type*} [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T]

/- /-- Change of coefficients in mv power series, as an `AlgHom` -/
def MvPowerSeries.mapAlgHom  (φ : S →ₐ[R] T) :
    MvPowerSeries σ S →ₐ[R] MvPowerSeries σ T where
  toRingHom   := MvPowerSeries.map σ φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

/-- Change of coefficients in power series, as an `AlgHom` -/
def PowerSeries.mapAlgHom (φ : S →ₐ[R] T) : PowerSeries S →ₐ[R] PowerSeries T :=
  MvPowerSeries.mapAlgHom φ

theorem MvPowerSeries.monomial_one_eq (e : σ →₀ ℕ) :
    MvPowerSeries.monomial R e 1 = e.prod fun s n ↦ (X s : MvPowerSeries σ R) ^ n := by
  simp only [← MvPolynomial.coe_X, ← MvPolynomial.coe_pow, ← MvPolynomial.coe_monomial,
    MvPolynomial.monomial_eq, map_one, one_mul]
  simp only [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, ← map_finsupp_prod]

theorem MvPowerSeries.prod_smul_X_eq_smul_monomial_one (S : Type*) [CommSemiring S] [Algebra R S]
    (e : σ →₀ ℕ) (a : σ → R) :
    e.prod (fun s n ↦ ((a s • X s : MvPowerSeries σ S) ^ n)) =
      (e.prod fun s n ↦ (a s) ^ n) • monomial S e 1 := by
  rw [Finsupp.prod_congr
    (g2 := fun s n ↦ ((C σ S (algebraMap R S (a s)) * (X s : MvPowerSeries σ S)) ^ n))]
  · have (a : R) (f : MvPowerSeries σ S) : a • f = (C σ S) ((algebraMap R S) a) * f := by
      rw [← smul_eq_C_mul, IsScalarTower.algebraMap_smul]
    simp only [mul_pow, Finsupp.prod_mul, ← map_pow , ← monomial_one_eq, this]
    simp only [map_finsupp_prod, map_pow]
  · intro x _
    rw [algebra_compatible_smul S, smul_eq_C_mul]

theorem MvPowerSeries.monomial_eq (e : σ →₀ ℕ) (r : σ → R) :
    MvPowerSeries.monomial R e (e.prod (fun s n => r s ^  n)) =
      (Finsupp.prod e fun s e => (r s • MvPowerSeries.X s) ^ e) := by
  rw [prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]

theorem MvPowerSeries.monomial_smul_const (e : σ →₀ ℕ) (r : R) :
    MvPowerSeries.monomial R e (r ^ (Finsupp.sum e fun _ n => n)) =
      (Finsupp.prod e fun s e => (r • MvPowerSeries.X s) ^ e) := by
  rw [prod_smul_X_eq_smul_monomial_one, ← map_smul, smul_eq_mul, mul_one]
  simp only [Finsupp.sum, Finsupp.prod, Finset.prod_pow_eq_pow_sum]
-/

section DiscreteUniformity

/-- The discrete uniformity -/
class DiscreteUniformity (α : Type*) [u : UniformSpace α] : Prop where
  eq_principal_idRel : uniformity α = Filter.principal idRel

/-- The bot uniformity is the discrete uniformity -/
instance (α : Type*) : @DiscreteUniformity α ⊥ := by
  apply @DiscreteUniformity.mk α ⊥ rfl

/-- The discrete uniformity induces the discrete topology  -/
instance (α : Type*) [UniformSpace α] [DiscreteUniformity α] :
    DiscreteTopology α := by
  rw [discreteTopology_iff_singleton_mem_nhds]
  intro a
  rw [UniformSpace.mem_nhds_iff]
  simp only [Set.subset_singleton_iff, DiscreteUniformity.eq_principal_idRel]
  simp only [Filter.mem_principal, idRel_subset]
  use Set.diagonal α
  simp only [Set.mem_diagonal_iff, implies_true, true_and]
  intro x
  simp only [UniformSpace.ball, Set.mem_preimage, Set.mem_diagonal_iff]
  exact fun a => a.symm

/-- The discrete uniformity makes a group a `UniformGroup -/
@[to_additive "The discrete uniformity makes an additive group a `UniformAddGroup`"]
instance {G : Type*} [Group G] [UniformSpace G] [DiscreteUniformity G] :
    IsUniformGroup G where
  uniformContinuous_div := fun s hs ↦ by
    simp only [uniformity_prod, DiscreteUniformity.eq_principal_idRel, Filter.comap_principal,
      Filter.inf_principal, Filter.map_principal, Filter.mem_principal, Set.image_subset_iff]
    rintro ⟨⟨x, y⟩, z, t⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, mem_idRel, and_imp]
    rintro ⟨rfl⟩ ⟨rfl⟩
    exact mem_uniformity_of_eq hs rfl

/-- The discrete uniformity makes a space complete -/
instance (α : Type*) [UniformSpace α] [DiscreteUniformity α] :
    CompleteSpace α where
  complete {f} hf := by
    simp [cauchy_iff, bot_uniformity] at hf
    rcases hf with ⟨f_NeBot, hf⟩
    let d := (fun (a : α) ↦ (a, a)) '' Set.univ
    obtain ⟨t, ht, ht'⟩ := hf d (by
      simp only [DiscreteUniformity.eq_principal_idRel, Filter.mem_principal, idRel_subset]
      exact (fun a ↦ Set.mem_image_of_mem (fun a => (a, a)) (Set.mem_univ a)))
    obtain ⟨x, hx⟩ := f_NeBot.nonempty_of_mem ht
    use x
    intro s hs
    apply f.sets_of_superset ht
    intro y hy
    convert mem_of_mem_nhds hs
    apply symm
    simpa only [d, Set.image_univ, Set.range_diag, Set.mem_diagonal_iff]
      using ht' (Set.mk_mem_prod hx hy)

end DiscreteUniformity

end Semiring

namespace MvPowerSeries

variable {σ A R τ S : Type*} [CommSemiring A] [CommRing R] [Algebra A R] [CommRing S] [Algebra A S]
  [Algebra R S] [IsScalarTower A R S]

open WithPiTopology

/-- Families of power series which can be substituted into other power series. -/
structure HasSubst (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff : ∀ s, IsNilpotent (constantCoeff τ S (a s))
  tendsto_zero : Filter.Tendsto a Filter.cofinite (@nhds _ (@instTopologicalSpace τ S ⊥) 0)

theorem hasSubst_X : HasSubst (fun (s : σ) ↦ (X s : MvPowerSeries σ S)) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun s ↦ by simp [constantCoeff_X, IsNilpotent.zero]
    tendsto_zero := variables_tendsto_zero }

theorem hasSubst_zero :
    HasSubst (fun (_ : σ) ↦ (0 : MvPowerSeries τ S)) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun _ ↦ by simp [Pi.zero_apply, map_zero, IsNilpotent.zero]
    tendsto_zero := tendsto_const_nhds }

theorem hasSubst_add {a b : σ → MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (a + b) where
  const_coeff := fun s ↦ by
    simp only [Pi.add_apply, map_add]
    exact (Commute.all _ _).isNilpotent_add (ha.const_coeff s) (hb.const_coeff s)
  tendsto_zero := by
    letI : UniformSpace S := ⊥
    convert Filter.Tendsto.add (ha.tendsto_zero) (hb.tendsto_zero)
    rw [add_zero]

/-
@[simp]
theorem constantCoeff_smul (φ : MvPowerSeries σ S) (a : R) :
    constantCoeff σ S (a • φ) = a • constantCoeff σ S φ :=
  rfl
-/

theorem hasSubst_mul (b : σ → MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (b * a) :=
  letI : UniformSpace S := ⊥
  { const_coeff := fun s ↦ by
      simp only [Pi.mul_apply, map_mul]
      exact Commute.isNilpotent_mul_right (Commute.all _ _) (ha.const_coeff _)
    tendsto_zero := IsLinearTopology.tendsto_mul_zero_of_right b a ha.tendsto_zero }

theorem hasSubst_smul (r : MvPowerSeries τ S) {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) := by convert hasSubst_mul _ ha

/-- Families of mv power series that can be substituted, as an `Ideal` -/
noncomputable def HasSubst.ideal : Ideal (σ → MvPowerSeries τ S) :=
  letI : UniformSpace S := ⊥
  { carrier := setOf HasSubst
    add_mem' := hasSubst_add
    zero_mem' := hasSubst_zero
    smul_mem' := hasSubst_mul }

/-- If `σ` is finite, then the nilpotency condition is enough for `HasSubst`. -/
theorem hasSubst_of_constantCoeff_nilpotent [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff τ S (a s))) :
    HasSubst a where
  const_coeff := ha
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- If σ is finite, then having zero constant coefficient is enough for HasSubst -/
theorem hasSubst_of_constantCoeff_zero [Finite σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff τ S (a s) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])

/-- Substitution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.eval₂ (algebraMap _ _) a f

variable {a : σ → MvPowerSeries τ S}

theorem HasSubst.hasEval (ha : HasSubst a) :
    @HasEval σ (MvPowerSeries τ S) _ (@instTopologicalSpace τ S ⊥) a :=
  letI : UniformSpace S := ⊥
  { hpow := fun s ↦
      isTopologicallyNilpotent_of_constantCoeff_isNilpotent (ha.const_coeff s)
    tendsto_zero := ha.tendsto_zero }

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom (ha : HasSubst a) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S := by
-- NOTE : Could there be a tactic that introduces these local instances?
  classical
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  exact MvPowerSeries.aeval ha.hasEval

@[simp]
theorem coe_substAlgHom (ha : HasSubst a) : ⇑(substAlgHom ha) = subst (R := R) a :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  coe_aeval (HasSubst.hasEval ha)

theorem subst_add (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]

theorem subst_mul (ha : HasSubst a) (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]

theorem subst_pow (ha : HasSubst a) (f : MvPowerSeries σ R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]

theorem subst_smul (ha : HasSubst a) (r : A) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]

theorem substAlgHom_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  aeval_coe ha.hasEval p

theorem substAlgHom_X (ha : HasSubst a) (s : σ) : substAlgHom (R := R) ha (X s) = a s := by
  rw [← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X]

theorem substAlgHom_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    substAlgHom ha (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← MvPolynomial.coe_monomial, substAlgHom_coe, MvPolynomial.aeval_monomial]

theorem subst_coe (ha : HasSubst a) (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

theorem subst_X (ha : HasSubst a) (s : σ) : subst (R := R) a (X s) = a s := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

theorem subst_monomial (ha : HasSubst a) (e : σ →₀ ℕ) (r : R) :
    subst a (monomial R e r) =
      (algebraMap R (MvPowerSeries τ S) r) * (e.prod (fun s n ↦ (a s) ^ n)) := by
  rw [← coe_substAlgHom ha, substAlgHom_monomial]

theorem continuous_subst (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  continuous_eval₂ (continuous_algebraMap _ _) ha.hasEval

theorem coeff_subst_finite (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  Set.Finite.support_of_summable _
    ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e)).summable

theorem coeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  have := ((hasSum_aeval ha.hasEval f).map (coeff S e) (continuous_coeff S e))
  erw [← coe_substAlgHom ha, ← this.tsum_eq, tsum_def]
  erw [dif_pos this.summable, if_pos (coeff_subst_finite ha f e)]
  rfl

theorem constantCoeff_subst (ha : HasSubst a) (f : MvPowerSeries σ R) :
    constantCoeff τ S (subst a f) =
      finsum (fun d ↦ (coeff R d f) • (constantCoeff τ S (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem map_algebraMap_eq_subst_X (f : MvPowerSeries σ R) :
    map σ (algebraMap R S) f = subst X f := by
  ext e
  rw [coeff_map, coeff_subst hasSubst_X f e, finsum_eq_single _ e]
  · rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_same,
      algebra_compatible_smul S, smul_eq_mul, mul_one]
  · intro d hd
    rw [← MvPowerSeries.monomial_one_eq, coeff_monomial_ne hd.symm, smul_zero]


variable {T : Type*} [CommRing T] [UniformSpace T] [T2Space T] [CompleteSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T] [Algebra R T] {ε : MvPowerSeries τ S →ₐ[R] T}

theorem comp_substAlgHom (ha : HasSubst a) :
    letI : UniformSpace S := ⊥
    letI : UniformSpace R := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) → ε.comp (substAlgHom ha) = aeval (HasEval.map hε ha.hasEval) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  fun hε ↦ comp_aeval ha.hasEval hε

theorem comp_subst (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) → ⇑ε ∘ (subst a) = ⇑(aeval (R := R) (HasEval.map hε ha.hasEval)) :=
  fun hε ↦ by rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, coe_substAlgHom]

theorem comp_subst_apply (ha : HasSubst a) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    haveI : ContinuousSMul R T := DiscreteTopology.instContinuousSMul R T
    (hε : Continuous ε) → (f : MvPowerSeries σ R) →
      ε (subst a f) = aeval (R := R) (HasEval.map hε ha.hasEval) f :=
  fun hε ↦ congr_fun (comp_subst ha hε)

variable [Algebra S T] [IsScalarTower R S T]

theorem eval₂_subst (ha : HasSubst a) {b : τ → T} (hb : HasEval b) (f : MvPowerSeries σ R) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s ↦ eval₂ (algebraMap S T) b (a s)) f := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  haveI : ContinuousSMul S T := DiscreteTopology.instContinuousSMul S T
  let ε : MvPowerSeries τ S →ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  simpa only [AlgHom.coe_restrictScalars', AlgHom.toRingHom_eq_coe,
    AlgHom.coe_restrictScalars, RingHom.coe_coe, ε, coe_aeval]
    using comp_subst_apply ha hε f

variable {υ : Type*} {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  {b : τ → MvPowerSeries υ S'}

-- TODO? : the converse holds when the kernel of `algebraMap R S` is a nilideal
theorem IsNilpotent_subst (ha : HasSubst a)
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff σ R f)) :
    IsNilpotent (constantCoeff τ S ((substAlgHom ha) f)) := by
  classical
  rw [coe_substAlgHom, constantCoeff_subst ha]
  apply IsNilpotent.finsum
  intro d
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    apply IsNilpotent.smul
    simp only [Finsupp.prod_zero_index, map_one, coeff_zero_eq_constantCoeff, smul_eq_mul, one_mul]
    exact IsNilpotent.map hf (algebraMap R S)
  · apply IsNilpotent.smul
    rw [← ne_eq, Finsupp.ne_iff] at hd
    obtain ⟨t, hs⟩ := hd
    rw [← Finsupp.prod_filter_mul_prod_filter_not (fun i ↦ i = t), map_mul,
      mul_comm, ← smul_eq_mul]
    apply IsNilpotent.smul
    rw [Finsupp.prod_eq_single t]
    · simp only [Finsupp.filter_apply_pos, map_pow]
      exact IsNilpotent.pow_of_pos (ha.const_coeff t) hs
    · intro t' htt' ht'
      simp only [Finsupp.filter_apply, if_neg ht', ne_eq, not_true_eq_false] at htt'
    · exact fun _ ↦ by rw [pow_zero]

theorem HasSubst.comp (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_subst hb (ha.const_coeff s)
  tendsto_zero := by
    letI : TopologicalSpace S := ⊥
    letI : TopologicalSpace S' := ⊥
    apply Filter.Tendsto.comp _ (ha.tendsto_zero)
    simp only [← map_zero (substAlgHom (R := S) hb), coe_substAlgHom]
    exact (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) := by
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  letI : UniformSpace S' := ⊥
  haveI : ContinuousSMul R S := DiscreteTopology.instContinuousSMul R S
  haveI : ContinuousSMul R (MvPowerSeries τ S) := DiscreteTopology.instContinuousSMul R (MvPowerSeries τ S)
  haveI : ContinuousSMul R S' := DiscreteTopology.instContinuousSMul R S'
  haveI : ContinuousSMul R (MvPowerSeries υ S') :=
    DiscreteTopology.instContinuousSMul R (MvPowerSeries υ S')
  apply comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R) ha.hasEval
  simp only [AlgHom.coe_restrictScalars', coe_substAlgHom]
  exact (continuous_subst (R := S) hb)

theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b)
    (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
  simpa only [funext_iff, coe_substAlgHom, DFunLike.ext_iff,
    AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply]
    using substAlgHom_comp_substAlgHom (R := R) ha hb

theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

section rescale

/-- Scale multivariate power series -/
noncomputable def rescale (a : σ → R) (f : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  subst (a • X) f

theorem rescale_eq_subst (a : σ → R) (f : MvPowerSeries σ R) :
    rescale a f = subst (a • X) f := rfl

variable (R) in
theorem hasSubst_rescale (a : σ → R) :
    HasSubst ((a • X) : σ → MvPowerSeries σ R) := by
  convert hasSubst_mul (fun s ↦ algebraMap R (MvPowerSeries σ R) (a s))
    hasSubst_X using 1
  rw [funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [algebra_compatible_smul (MvPowerSeries σ R), smul_eq_mul]

variable (R) in
/-- Scale multivariate power series, as an `AlgHom` -/
noncomputable def rescaleAlgHom (a : σ → R) :
    MvPowerSeries σ R →ₐ[R] MvPowerSeries σ  R :=
  substAlgHom (hasSubst_rescale R a)

theorem coe_rescaleAlgHom (a : σ → R) :
    ⇑(rescaleAlgHom R a) = rescale a :=
  coe_substAlgHom (hasSubst_rescale R a)

theorem rescaleAlgHom_comp (a b : σ → R) :
    (rescaleAlgHom R a).comp (rescaleAlgHom R b) = rescaleAlgHom R (a * b) := by
  rw [AlgHom.ext_iff]
  intro f
  simp only [AlgHom.coe_comp, Function.comp_apply, rescaleAlgHom,
    substAlgHom_comp_substAlgHom_apply]
  congr
  rw [funext_iff]
  intro s
  simp only [Pi.smul_apply', Pi.mul_apply]
  rw [AlgHom.map_smul_of_tower, ← MvPolynomial.coe_X, substAlgHom_coe, MvPolynomial.aeval_X,
    MvPolynomial.coe_X]
  simp [Pi.smul_apply', algebraMap_smul, ← mul_smul, mul_comm]

theorem rescale_rescale_apply (a b : σ → R) (f : MvPowerSeries σ R) :
    (f.rescale b).rescale a = f.rescale (a * b) := by
  simp only [← coe_rescaleAlgHom, ← AlgHom.comp_apply, rescaleAlgHom_comp]

theorem coeff_rescale (r : σ → R) (f : MvPowerSeries σ R) (d : σ →₀ ℕ) :
    coeff R d (rescale r f) = (d.prod fun s n ↦ r s ^ n) • coeff R d f := by
  unfold rescale
  rw [coeff_subst (hasSubst_rescale R _)]
  simp only [Pi.smul_apply', smul_eq_mul, prod_smul_X_eq_smul_monomial_one]
  simp only [LinearMap.map_smul_of_tower, Algebra.mul_smul_comm]
  rw [finsum_eq_single _ d]
  · simp only [coeff_monomial_same, mul_one, smul_eq_mul]
  · intro e he
    simp only [coeff_monomial_ne he.symm, mul_zero, smul_zero]

theorem rescale_one :
    rescale 1 = @id (MvPowerSeries σ R) := by
  ext f d
  simp only [coeff_rescale, Finsupp.prod, Pi.one_apply, one_pow, Finset.prod_const_one, smul_eq_mul,
    one_mul, id_eq]

theorem rescaleAlgHom_one :
    rescaleAlgHom R 1 = AlgHom.id R (MvPowerSeries σ R):= by
  rw [DFunLike.ext_iff]
  intro f
  simp only [Function.const_one, coe_rescaleAlgHom, AlgHom.coe_id, id_eq, rescale_one]

/-- Scale mv power series, as a `MonoidHom` in the scaling parameters -/
noncomputable def rescaleMonoidHom : (σ → R) →* MvPowerSeries σ R →ₐ[R] MvPowerSeries σ R where
  toFun := rescaleAlgHom R
  map_one' := rescaleAlgHom_one
  map_mul' a b := by simp only [← rescaleAlgHom_comp, AlgHom.End_toSemigroup_toMul_mul]

theorem rescale_zero_apply (f : MvPowerSeries σ R) :
    rescale 0 f = MvPowerSeries.C σ R (constantCoeff σ R f) := by
  classical
  ext d
  simp only [coeff_rescale, coeff_C]
  by_cases hd : d = 0
  · simp only [hd, Pi.zero_apply, Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff,
      smul_eq_mul, one_mul, ↓reduceIte]
  · simp only [Pi.zero_apply, smul_eq_mul, if_neg hd]
    convert zero_smul R _
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨s, hs⟩ := hd
    apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
    simp [Function.const_apply, zero_pow hs]

/-- Scaling a linear power series is smul -/
lemma rescale_linear_eq_smul (r : R) (f : MvPowerSeries σ R)
    (hf : ∀ (d : σ →₀ ℕ), (d.sum (fun _ n ↦ n) ≠ 1) → MvPowerSeries.coeff R d f = 0) :
    MvPowerSeries.rescale (Function.const σ r) f = r • f := by
  ext e
  simp only [MvPowerSeries.coeff_rescale, map_smul]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, smul_eq_mul]
  by_cases he : Finsupp.sum e (fun _ n ↦ n) = 1
  · simp only [Finsupp.sum] at he
    simp [he, pow_one]
  · simp [hf e he, mul_zero]

open PowerSeries

theorem rescale_unit (a : R) (f : R⟦X⟧) :
    MvPowerSeries.rescale (Function.const _ a) f = PowerSeries.rescale a f := by
  ext d
  change MvPowerSeries.coeff R _ _ = _
  rw [PowerSeries.coeff_rescale, coeff_rescale, smul_eq_mul]
  simp only [Function.const_apply, pow_zero, Finsupp.prod_single_index, PowerSeries.coeff]

end rescale

end MvPowerSeries
