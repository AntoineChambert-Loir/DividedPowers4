import Mathlib.Topology.Algebra.Algebra
import Mathlib.Data.MvPolynomial.CommRing
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc
import DividedPowers.ForMathlib.MvPowerSeries.Evaluation
import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology
import DividedPowers.ForMathlib.Topology.Algebra.Algebra.Basic

--import Mathlib.Topology.UniformSpace.CompleteSeparated

/- # Substitutions in power series

Here we define the substitution of power series into other power series.
We follow Bourbaki, Algèbre, chap. 4, §4, n° 3.

Evaluation of a power series at adequate elements has been defined
in `DividedPowers.ForMathlib.MvPowerSeries.Evaluation.lean`.
The goal here is to check the relevant hypotheses:
* The ring of coefficients is endowed the discrete topology.
* The main condition rewrites as having vanishing constant coefficient
* Power series have a linear topology
-/

theorem Set.Finite.support_of_summable
    {α : Type*} [AddCommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    {β : Type*} (f : β → α) (h : Summable f) : Set.Finite f.support := by
  obtain ⟨a, ha⟩ := h
  simp only [HasSum] at ha
  classical
  simp_rw [tendsto_atTop_nhds] at ha
  obtain ⟨s, hs⟩ := ha {a} rfl (isOpen_discrete _)
  apply Set.Finite.subset s.finite_toSet
  intro b
  rw [Function.mem_support, not_imp_comm]
  intro hb
  let hs' := hs (insert b s) (s.subset_insert b)
  specialize hs s (subset_of_eq rfl)
  simp only [Set.mem_singleton_iff] at hs hs'
  simpa [Finset.sum_insert hb, hs, add_left_eq_self] using hs'

theorem add_pow_add_pred_eq_zero_of_pow_eq_zero {α : Type*} [CommSemiring α]
    {a b : α} {m n : ℕ} (ha : a ^ m = 0) (hb : b ^ n = 0) :
    (a + b) ^ (m + n).pred = 0 := by
  rw [add_pow]
  apply Finset.sum_eq_zero
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases h : k < m
  · have : n ≤ (m + n).pred - k  := by
      rw [Nat.le_sub_iff_add_le (Nat.le_of_lt_succ hk), add_comm]
      rw [Nat.le_pred_iff_lt (lt_of_le_of_lt (zero_le k) (Nat.lt_add_right n h))]
      exact Nat.add_lt_add_right h n
    rw [← Nat.add_sub_of_le this, pow_add, hb]
    simp only [zero_mul, mul_zero]
  · simp only [not_lt] at h
    rw [← Nat.add_sub_of_le h, pow_add, ha]
    simp only [zero_mul]

theorem IsNilpotent.add {α : Type*} [CommSemiring α]
    {a b : α} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (a + b) := by
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  exact ⟨_, add_pow_add_pred_eq_zero_of_pow_eq_zero ha hb⟩

theorem IsNilpotent.finset_sum {α : Type*} [CommSemiring α] {β : Type*} {f : β → α}
    (s : Finset β) (hf : ∀ b ∈ s, IsNilpotent (f b)) :
    IsNilpotent (s.sum f) := by
  classical
  induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, IsNilpotent.zero]
    | @insert b s hb hs =>
      rw [Finset.sum_insert hb]
      apply IsNilpotent.add
      exact hf b (s.mem_insert_self b)
      exact hs (fun b hb ↦ hf b (by exact Finset.mem_insert_of_mem hb))

theorem IsNilpotent.finsum {α : Type*} [CommSemiring α] {β : Type*} (f : β → α)
  (hf : ∀ b, IsNilpotent (f b)) : IsNilpotent (finsum f) := by
  classical
  by_cases h : Set.Finite f.support
  · rw [finsum_def, dif_pos h]
    exact IsNilpotent.finset_sum _ (fun b _ ↦ hf b)
  · simp only [finsum_def, dif_neg h, IsNilpotent.zero]


def MvPowerSeries.mapAlgHom (σ : Type*) {R : Type*} [CommSemiring R]
  {S : Type*} [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
  (φ : S →ₐ[R] T) :
  MvPowerSeries σ S →ₐ[R] MvPowerSeries σ T where
  toRingHom := MvPowerSeries.map σ φ
  commutes' := sorry

def PowerSeries.mapAlgHom {R : Type*} [CommSemiring R]
  {S : Type*} [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T]
  (φ : S →ₐ[R] T) :
  PowerSeries S →ₐ[R] PowerSeries T := MvPowerSeries.mapAlgHom Unit φ

section DiscreteUniformity

class DiscreteUniformity (α : Type*) [u : UniformSpace α] : Prop where
  eq_principal_idRel : uniformity α = Filter.principal idRel

instance discreteUniformity_bot (α : Type*) : @DiscreteUniformity α ⊥ := by
  apply @DiscreteUniformity.mk α ⊥ rfl

instance discreteTopology_of_discreteUniformity (α : Type*)
    [UniformSpace α] [DiscreteUniformity α] : DiscreteTopology α := by
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

instance bot_uniformAddGroup {R : Type*} [AddGroup R]
    [UniformSpace R] [DiscreteUniformity R] : UniformAddGroup R :=
  { uniformContinuous_sub := fun s hs ↦ by
      simp only [uniformity_prod, DiscreteUniformity.eq_principal_idRel, Filter.comap_principal,
        Filter.inf_principal, Filter.map_principal, Filter.mem_principal, Set.image_subset_iff]
      rintro ⟨⟨x, y⟩, z, t⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, mem_idRel, and_imp]
      rintro ⟨rfl⟩ ⟨rfl⟩
      exact mem_uniformity_of_eq hs rfl }

instance discreteUniformity_complete (α : Type*) [UniformSpace α] [DiscreteUniformity α] : CompleteSpace α :=
  { complete := fun {f} hf ↦ by
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
      simpa only [d, Set.image_univ, Set.range_diag, Set.mem_diagonal_iff] using ht' (Set.mk_mem_prod hx hy)
      }

end DiscreteUniformity

namespace MvPowerSeries

variable {σ : Type*} [DecidableEq σ]
  {R : Type*} [CommRing R]
  -- [TopologicalSpace α] [TopologicalRing α]
  {τ : Type*} [DecidableEq τ]
  {S : Type*} [CommRing S] [Algebra R S]
  -- [TopologicalSpace R] [TopologicalRing R][TopologicalAlgebra α R]

variable {a : σ → MvPowerSeries τ S} (ha : SubstDomain a)

open WithPiTopology WithPiUniformity

local instance : UniformSpace R := ⊥
-- local instance : DiscreteUniformity R := discreteUniformity_bot R
-- local instance : UniformAddGroup R := bot_uniformAddGroup
-- local instance : DiscreteTopology R := discreteTopology_bot R
local instance : TopologicalRing R := DiscreteTopology.topologicalRing

local instance : UniformSpace S := ⊥
local instance : DiscreteUniformity S := discreteUniformity_bot S
-- local instance : CompleteSpace S := discreteUniformity_complete S
-- local instance : DiscreteTopology S := discreteTopology_bot S
-- local instance : UniformAddGroup S := bot_uniformAddGroup
local instance : TopologicalAlgebra R S := inferInstance

-- local instance : UniformSpace (MvPowerSeries τ S) := uniformSpace τ S
-- local instance : UniformAddGroup (MvPowerSeries τ S) := uniformAddGroup τ S
noncomputable local instance : LinearTopology (MvPowerSeries τ S) := isLinearTopology τ S
-- local instance : T2Space (MvPowerSeries τ S) := t2Space τ S
-- local instance : TopologicalRing (MvPowerSeries τ S) := topologicalRing _ _
noncomputable local instance : TopologicalAlgebra R (MvPowerSeries τ S) := by
    refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
local instance : CompleteSpace (MvPowerSeries τ S) := by refine completeSpace τ S

/-- Families of power series which can be substituted -/
structure SubstDomain (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff : ∀ s, IsNilpotent (constantCoeff τ S (a s))
  tendsto_zero : Filter.Tendsto a Filter.cofinite (nhds 0)

/-- If σ is finite, then the nilpotent condition is enough for SubstDomain -/
def substDomain_of_constantCoeff_nilpotent [Fintype σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff τ S (a s))) :
    SubstDomain a where
  const_coeff := ha
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- If σ is finite, then having zero constant coefficient is enough for SubstDomain -/
def substDomain_of_constantCoeff_zero [Fintype σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff τ S (a s) = 0) :
    SubstDomain a :=
  substDomain_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])

/-- Substitution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  MvPowerSeries.eval₂ (algebraMap _ _) a f

def SubstDomain.evalDomain : EvalDomain a := {
  hpow := fun s ↦ (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s)
  tendsto_zero := ha.tendsto_zero }

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.aeval ha.evalDomain

theorem coe_subst : subst a = ⇑(substAlgHom (R := R) ha) := rfl

theorem subst_coe (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  refine aeval_coe ha.evalDomain p

theorem continuous_subst : Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) :=
  continuous_aeval ha.evalDomain

theorem coeff_subst_finite (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  Set.Finite.support_of_summable _
    ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff e)).summable

theorem coeff_subst (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) = finsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
  have := ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff e))
  erw [← this.tsum_eq, tsum_def]
  erw [dif_pos this.summable, if_pos (coeff_subst_finite ha f e)]
  rfl

theorem constantCoeff_subst (f : MvPowerSeries σ R) :
    constantCoeff τ S (subst a f) = finsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (constantCoeff τ S (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

variable
    {T : Type*} [CommRing T] [UniformSpace T] [UniformAddGroup T]
    [LinearTopology T] [T2Space T] [TopologicalRing T] [TopologicalAlgebra R T] [CompleteSpace T]
    {ε : MvPowerSeries τ S →ₐ[R] T} (hε : Continuous ε)

theorem comp_substAlgHom :
   ε.comp (substAlgHom ha) = aeval (EvalDomain.map hε ha.evalDomain) :=
  comp_aeval ha.evalDomain hε

theorem comp_subst :=
--    ⇑ε ∘ (subst a) = subst (EvalDomain.map hε ha.evalDomain) :=
  comp_aeval ha.evalDomain hε



/- a : σ → MvPowerSeries τ S
   b : τ → MvPowerSeries υ T
   f ∈ R⟦σ⟧, f(a) = substAlgHom ha f ∈ S⟦τ⟧
   f(a) (b) = substAlgHom hb (substAlgHom ha f)
   f = X s, f (a) = a s
   f(a) (b) = substAlgHom hb (a s)
   -/

variable {υ : Type*} [DecidableEq υ]
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {b : τ → MvPowerSeries υ T} (hb : SubstDomain b)

-- TODO : prove equivalence (constant coefficient of f is nilpotent iff ...)-/
theorem IsNilpotent_subst
    {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff σ R f)) :
    IsNilpotent (constantCoeff τ S ((substAlgHom ha) f)) := by
  rw [← coe_subst ha, constantCoeff_subst ha]
  apply IsNilpotent.finsum
  intro d
  by_cases hd : d = 0
  · rw [← algebraMap_smul S, smul_eq_mul, mul_comm, ← smul_eq_mul, hd]
    exact IsNilpotent.smul (IsNilpotent.map hf _) _
  · apply IsNilpotent.smul
    have : ∃ s, d s ≠ 0 := by
      by_contra hd'
      apply hd
      simp only [ne_eq, not_exists, not_not] at hd'
      ext x; exact hd' x
    obtain ⟨t, hs⟩ := this
    rw [← Finsupp.prod_filter_mul_prod_filter_not (fun i ↦ i = t), map_mul]
    rw [mul_comm, ← smul_eq_mul]
    apply IsNilpotent.smul
    rw [Finsupp.prod_eq_single t]
    simp only [Finsupp.filter_apply_pos, map_pow]
    exact IsNilpotent.pow_of_pos (ha.const_coeff t) hs
    intro t' htt' ht'
    simp only [Finsupp.filter_apply, if_neg ht', ne_eq, not_true_eq_false] at htt'
    exact fun _ ↦ by rw [pow_zero]

def SubstDomain.comp : SubstDomain (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_subst hb (ha.const_coeff s)
  tendsto_zero := by
    apply Filter.Tendsto.comp _ (ha.tendsto_zero)
    rw [← coe_subst, ← (substAlgHom (R := S) hb).map_zero]
    apply (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom  ha)
      = substAlgHom (ha.comp hb) := by
  apply comp_aeval ha.evalDomain
  apply continuous_subst hb

theorem substAlgHom_comp_substAlgHom_apply (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom  ha f)
      = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
  have h := substAlgHom_comp_substAlgHom (R := R) ha hb
  simp only [DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply] at h
  apply funext
  exact h

theorem subst_comp_subst_apply (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

/-  Not the needed function
theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  := by
  apply MvPowerSeries.comp_aeval
  sorry
-/
end MvPowerSeries

namespace PowerSeries

variable {R : Type*} [CommRing R]
  {τ : Type*} [DecidableEq τ]
  {S : Type*} [CommRing S] [Algebra R S]

open MvPowerSeries.WithPiTopology MvPowerSeries.WithPiUniformity

local instance : UniformSpace R := ⊥
-- local instance : DiscreteUniformity R := discreteUniformity_bot R
-- local instance : UniformAddGroup R := bot_uniformAddGroup
-- local instance : DiscreteTopology R := discreteTopology_bot R
local instance : TopologicalRing R := DiscreteTopology.topologicalRing

local instance : UniformSpace S := ⊥
local instance : DiscreteUniformity S := discreteUniformity_bot S
local instance : TopologicalAlgebra R S := inferInstance

noncomputable local instance : LinearTopology (MvPowerSeries τ S) := MvPowerSeries.isLinearTopology τ S
noncomputable local instance : TopologicalAlgebra R (MvPowerSeries τ S) := by
    refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
local instance : CompleteSpace (MvPowerSeries τ S) := by refine completeSpace τ S

/-- Families of power series which can be substituted -/
structure SubstDomain (a : MvPowerSeries τ S) : Prop where
  const_coeff : IsNilpotent (MvPowerSeries.constantCoeff τ S a)

def substDomain_of_constantCoeff_nilpotent
    {a : MvPowerSeries τ S}
    (ha : IsNilpotent (MvPowerSeries.constantCoeff τ S a)) :
    SubstDomain a where
  const_coeff := ha

def substDomain_of_constantCoeff_zero
    {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff τ S a = 0) :
    SubstDomain a where
  const_coeff := by simp only [ha, IsNilpotent.zero]

def SubstDomain.map {T : Type*} [CommRing T] [Algebra R T]
    (ε : S →ₐ[R] T)
    {a : MvPowerSeries τ S} (ha : SubstDomain a) :
    SubstDomain (MvPowerSeries.map τ ε.toRingHom a) where
  const_coeff := sorry

variable {υ : Type*} [DecidableEq υ]
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Substitution of power series into a power series -/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S} (ha : SubstDomain a)

def SubstDomain.const : MvPowerSeries.SubstDomain (fun (_ : Unit) ↦ a) where
  const_coeff := fun _ ↦ ha.const_coeff
  tendsto_zero := sorry

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom : PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_subst : subst a = ⇑(substAlgHom (R := R) ha) := rfl

theorem subst_coe (p : Polynomial R) :
    subst (R := R) a (p : PowerSeries R) = Polynomial.aeval a p :=
  sorry

theorem comp_subst
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_subst ha.const ε

theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_substAlgHom ha.const ε

def SubstDomain.comp {a : PowerSeries S} (ha : SubstDomain a)
    {b : MvPowerSeries υ T} (hb : SubstDomain b):
    SubstDomain (substAlgHom hb a) where
  const_coeff := sorry

theorem substAlgHom_comp_substAlgHom
    {υ : Type*} [DecidableEq υ] {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {a : PowerSeries S} (ha : SubstDomain a)
    {b : MvPowerSeries υ T} (hb : SubstDomain b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom  ha)
      = substAlgHom (ha.comp hb) := by
  apply comp_aeval ha.evalDomain
  apply continuous_subst hb

theorem substAlgHom_comp_substAlgHom_apply
    {υ : Type*} [DecidableEq υ] {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {b : τ → MvPowerSeries υ T} (hb : SubstDomain b) (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom  ha f)
      = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst
    {υ : Type*} [DecidableEq υ] {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {b : τ → MvPowerSeries υ T} (hb : SubstDomain b) :
    (subst b) ∘ (subst a)
      = subst (R := R) (fun s ↦ subst b (a s)) := by
  have h := substAlgHom_comp_substAlgHom (R := R) ha hb
  simp only [DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply] at h
  apply funext
  exact h

theorem subst_comp_subst_apply
    {υ : Type*} [DecidableEq υ] {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {b : τ → MvPowerSeries υ T} (hb : SubstDomain b) (f : MvPowerSeries σ R) :
    subst b (subst a f) = subst (fun s ↦ subst b (a s)) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f


end PowerSeries

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

/-- A power series f : R⟦T⟧ is exponential if f(X + Y) = f(X) f(Y)
(one should add f(0) = 1) -/
def IsExponential (f : PowerSeries R) :=
  PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) R) f
    = PowerSeries.subst (X 0) f * PowerSeries.subst (X 1) f

/-- If f and g are exponential, then so is f * g -/
example (f g : MvPowerSeries Unit R) (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) := by
  simp only [IsExponential] at hf hg ⊢
  repeat
    rw [PowerSeries.coe_subst (PowerSeries.substDomain_of_constantCoeff_zero (by simp))]
  simp only [map_mul, ← PowerSeries.coe_subst, hf, hg]
  ring

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
  rw [PowerSeries.coe_subst (PowerSeries.substDomain_of_constantCoeff_zero (by simp [constantCoeff_smul, constantCoeff_X, smul_zero]))]
  rw [PowerSeries.coe_subst
    (PowerSeries.substDomain_of_constantCoeff_zero (by
      erw [constantCoeff_smul, constantCoeff_X, smul_zero]))]
  rw [PowerSeries.coe_subst (PowerSeries.substDomain_of_constantCoeff_zero (by simp only [Fin.isValue, constantCoeff_X]))]
  rw [PowerSeries.coe_subst (PowerSeries.substDomain_of_constantCoeff_zero (by simp only [Fin.isValue, constantCoeff_X]))]
  unfold PowerSeries.substAlgHom
  classical
  erw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply ?_ ?_ f]


  simp only [Fin.isValue, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
    Submodule.coe_smul_of_tower, coe_T]
  rw [this]
  rw [← foo2 r]
  rw [← subst_comp_subst_apply]
  simp [← coe_subst, coe_T] at hf
  rw [hf]
  rw [coe_subst ?_, map_mul, ← coe_subst]
  apply congr_arg₂
  rw [subst_comp_subst_apply]
  apply congr_arg₂ _ _ rfl
  ext s


  -- simp_rw [congr_arg₂ (foo1 r) f]
  /- f (r • (X + Y)))
      = f (r • X + r • Y)
      = f(r • X) f(r • Y)

    -/
--  have : SubstDomain.comp (Dom.substDomain (r • T ())) (Dom.substDomain (T 0 + T 1)) = Dom.substDomain (r • T 1 + r • T 1) := by sorry
  sorry

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
