import Mathlib.Topology.Algebra.Algebra
import Mathlib.Algebra.MvPolynomial.CommRing
import DividedPowers.ForMathlib.RingTheory.MvPowerSeries.Trunc
import DividedPowers.ForMathlib.MvPowerSeries.Evaluation
import DividedPowers.ForMathlib.MvPowerSeries.LinearTopology
import DividedPowers.ForMathlib.PowerSeries.Topology
import DividedPowers.ForMathlib.Topology.Algebra.Algebra.Basic
import Mathlib.Data.Set.Finite

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


def MvPowerSeries.mapAlgHom (σ : Type*) {R : Type*} [CommSemiring R] {S : Type*}
    [Semiring S] [Algebra R S] {T : Type*} [Semiring T] [Algebra R T] (φ : S →ₐ[R] T) :
    MvPowerSeries σ S →ₐ[R] MvPowerSeries σ T where
  toRingHom   := MvPowerSeries.map σ φ
  commutes' r := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, MvPowerSeries.algebraMap_apply, map_C, RingHom.coe_coe, AlgHom.commutes]

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


open WithPiTopology WithPiUniformity

/-- Families of power series which can be substituted -/
structure SubstDomain (a : σ → MvPowerSeries τ S) : Prop where
  const_coeff : ∀ s, IsNilpotent (constantCoeff τ S (a s))
  tendsto_zero : Filter.Tendsto a Filter.cofinite (@nhds _ (@topologicalSpace τ S ⊥) 0)

#check SubstDomain

/-
--variable [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

noncomputable local instance : LinearTopology (MvPowerSeries τ S) := isLinearTopology τ S
noncomputable local instance : TopologicalAlgebra R (MvPowerSeries τ S) := by
    refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
local instance : CompleteSpace (MvPowerSeries τ S) := by refine completeSpace τ S -/

/-- If σ is finite, then the nilpotent condition is enough for SubstDomain -/
def substDomain_of_constantCoeff_nilpotent [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, IsNilpotent (constantCoeff τ S (a s))) :
    SubstDomain a where
  const_coeff := ha
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- If σ is finite, then having zero constant coefficient is enough for SubstDomain -/
def substDomain_of_constantCoeff_zero [Finite σ]
    {a : σ → MvPowerSeries τ S} (ha : ∀ s, constantCoeff τ S (a s) = 0) :
    SubstDomain a :=
  substDomain_of_constantCoeff_nilpotent (fun s ↦ by simp only [ha s, IsNilpotent.zero])

/-- Substitution of power series into a power series -/
noncomputable def subst (a : σ → MvPowerSeries τ S) (f : MvPowerSeries σ R) :
    MvPowerSeries τ S :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  MvPowerSeries.eval₂ (algebraMap _ _) a f

variable {a : σ → MvPowerSeries τ S} (ha : SubstDomain a)

def SubstDomain.evalDomain : @EvalDomain σ (MvPowerSeries τ S) _ (@topologicalSpace τ S ⊥) a :=
  letI : UniformSpace S := ⊥
  letI : DiscreteUniformity S := discreteUniformity_bot S
  { hpow := fun s ↦ (tendsto_pow_of_constantCoeff_nilpotent_iff (a s)).mpr (ha.const_coeff s)
    tendsto_zero := ha.tendsto_zero }

-- NOTE: We need `by exact` or the proof breaks!!!!
/-- Substitution of power series into a power series -/
noncomputable def substAlgHom : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ S := by
  letI : UniformSpace R := ⊥
  letI : DiscreteUniformity R := discreteUniformity_bot R
  letI : UniformSpace S := ⊥
  letI : DiscreteUniformity S := discreteUniformity_bot S
  -- letI : LinearTopology (MvPowerSeries τ S) := isLinearTopology τ S
  -- letI : TopologicalAlgebra R (MvPowerSeries τ S) := by
  --   refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
  --NOTE : Could there be a tactic that introduces these local instances?
  exact MvPowerSeries.aeval ha.evalDomain

theorem coe_subst : subst a = ⇑(substAlgHom (R := R) ha) := rfl

variable {ha}
theorem substAlgHom_apply (f : MvPowerSeries σ R) :
  substAlgHom ha f = subst a f := rfl

variable (ha)
theorem subst_add (f g : MvPowerSeries σ R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [coe_subst ha, map_add]

theorem subst_mul (f g : MvPowerSeries σ R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [coe_subst ha, map_mul]

theorem subst_pow (f : MvPowerSeries σ R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [coe_subst ha, map_pow]

theorem subst_smul (r : R) (f : MvPowerSeries σ R) :
    subst a (r • f) = r • (subst a f) := by
  rw [coe_subst ha, map_smul]

theorem substAlgHom_coe (p : MvPolynomial σ R) :
    substAlgHom (R := R) ha p = MvPolynomial.aeval a p :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  aeval_coe ha.evalDomain p

theorem subst_coe (p : MvPolynomial σ R) :
    subst (R := R) a p = MvPolynomial.aeval a p := by
  rw [← substAlgHom_apply (ha := ha), substAlgHom_coe]

theorem continuous_subst :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ S) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  continuous_aeval ha.evalDomain

theorem coeff_subst_finite (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    Set.Finite (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))).support :=
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  Set.Finite.support_of_summable _
    ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff e)).summable

theorem coeff_subst (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff S e (subst a f) = finsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (coeff S e (d.prod fun s e => (a s) ^ e))) := by
  letI : UniformSpace S := ⊥
  letI : UniformSpace R := ⊥
  have := ((hasSum_aeval ha.evalDomain f).map (coeff S e) (continuous_coeff e))
  erw [← this.tsum_eq, tsum_def]
  erw [dif_pos this.summable, if_pos (coeff_subst_finite ha f e)]
  rfl

theorem constantCoeff_subst (f : MvPowerSeries σ R) :
    constantCoeff τ S (subst a f) = finsum (fun (d : σ →₀ ℕ) ↦ (coeff R d f) • (constantCoeff τ S (d.prod fun s e => (a s) ^ e))) := by
  simp only [← coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

variable
    {T : Type*} [CommRing T]
    [UniformSpace T] [T2Space T] [CompleteSpace T]
    [UniformAddGroup T] [TopologicalRing T] [LinearTopology T]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {ε : MvPowerSeries τ S →ₐ[R] T}

theorem comp_substAlgHom :
    letI : UniformSpace S := ⊥
    letI : UniformSpace R := ⊥
    (hε : Continuous ε) →
      ε.comp (substAlgHom ha) = aeval (EvalDomain.map hε ha.evalDomain) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  fun hε ↦ comp_aeval ha.evalDomain hε

theorem comp_subst :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    (hε : Continuous ε) →
      ⇑ε ∘ (subst a) = ⇑(aeval (R := R) (EvalDomain.map hε ha.evalDomain)) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  fun hε ↦ by rw [← comp_substAlgHom ha hε, AlgHom.coe_comp, ← coe_subst]

theorem comp_subst_apply :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    (hε : Continuous ε) → (f : MvPowerSeries σ R) →
      ε (subst a f) = aeval (R := R) (EvalDomain.map hε ha.evalDomain) f :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  fun hε ↦ congr_fun (comp_subst ha hε)

theorem eval₂_subst {b : τ → T} (hb : EvalDomain b) (f : MvPowerSeries σ R) :
    letI : UniformSpace R := ⊥
    letI : UniformSpace S := ⊥
    eval₂ (algebraMap S T) b (subst a f) =
      eval₂ (algebraMap R T) (fun s ↦ eval₂ (algebraMap S T) b (a s)) f :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  let ε : MvPowerSeries τ S →ₐ[R] T := (aeval hb).restrictScalars R
  have hε : Continuous ε := continuous_aeval hb
  comp_subst_apply ha hε f

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

-- TODO? : the converse holds when the kernel of `algebraMap R S` is a nilideal
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

def SubstDomain.comp : SubstDomain (fun s ↦ substAlgHom hb (a s)) where
  const_coeff s := IsNilpotent_subst hb (ha.const_coeff s)
  tendsto_zero := by
    letI : TopologicalSpace S := ⊥
    letI : TopologicalSpace T := ⊥
    apply Filter.Tendsto.comp _ (ha.tendsto_zero)
    rw [← coe_subst, ← (substAlgHom (R := S) hb).map_zero]
    apply (continuous_subst hb).continuousAt

theorem substAlgHom_comp_substAlgHom :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) :=
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  letI : UniformSpace T := ⊥
  comp_aeval (R := R) (ε := (substAlgHom hb).restrictScalars R)
    ha.evalDomain (continuous_subst (R := S) hb)

theorem substAlgHom_comp_substAlgHom_apply (f : MvPowerSeries σ R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst :
    (subst b) ∘ (subst a) = subst (R := R) (fun s ↦ subst b (a s)) := by
  apply funext
  simpa only [DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply] using
    substAlgHom_comp_substAlgHom (R := R) ha hb

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

open MvPowerSeries.WithPiUniformity WithPiTopology
/-
local instance us : UniformSpace R := ⊥
local instance : TopologicalRing R := DiscreteTopology.topologicalRing

local instance us2 : UniformSpace S := ⊥
local instance : DiscreteUniformity S := discreteUniformity_bot S
local instance : TopologicalAlgebra R S := inferInstance -/

-- variable [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

/- noncomputable local instance : LinearTopology (MvPowerSeries τ S) :=
  MvPowerSeries.WithPiTopology.isLinearTopology τ S
-/

--noncomputable local instance : TopologicalSpace (PowerSeries S) := inferInstance

-- TODO : PowerSeries.LinearTopology file
/- noncomputable local instance : LinearTopology (PowerSeries S) :=
   MvPowerSeries.isLinearTopology Unit S
-/

/- noncomputable local instance : TopologicalAlgebra R (MvPowerSeries τ S) := by
    refine DiscreteTopology.topologicalAlgebra R (MvPowerSeries τ S)
local instance : CompleteSpace (MvPowerSeries τ S) := by refine completeSpace τ S
-/

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

variable {υ : Type*} [DecidableEq υ]
  {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Substitution of power series into a power series -/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f

variable {a : MvPowerSeries τ S} (ha : SubstDomain a)

def SubstDomain.const : MvPowerSeries.SubstDomain (fun (_ : Unit) ↦ a) where
  const_coeff  := fun _ ↦ ha.const_coeff
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

/-- Substitution of power series into a power series -/
noncomputable def substAlgHom  : PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const

theorem coe_subst : subst a = ⇑(substAlgHom (R := R) ha) := rfl

variable {ha}
theorem substAlgHom_apply (f : PowerSeries R) :
  substAlgHom ha f = subst a f := rfl

variable (ha)

theorem subst_add (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [coe_subst ha, map_add]

theorem subst_pow (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f ) ^ n := by
  rw [coe_subst ha, map_pow]


theorem subst_mul (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [coe_subst ha, map_mul]

theorem subst_smul (r : R) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [coe_subst ha, map_smul]

/-
-- TODO LIST:
- Add PowerSeries.toMvPowerSeries_Unit
- Show it is a topological equivalence.
- The support under finsuppUnitEquiv should be the image of the support.
-/

theorem coeff_subst_finite (f : PowerSeries R) (e : τ →₀ ℕ) :
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

theorem coeff_subst (f : PowerSeries R) (e : τ →₀ ℕ) :
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

theorem constantCoeff_subst (f : PowerSeries R) :
    MvPowerSeries.constantCoeff τ S (subst a f) =
    finsum (fun (d : ℕ) ↦ (coeff R d f) •
      (MvPowerSeries.constantCoeff τ S (a ^ d))) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) :
    (p : PowerSeries R) =
      ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) := by
  change (Polynomial.coeToPowerSeries.algHom R) p =
    (MvPolynomial.coeToMvPowerSeries.algHom R) (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R) p)
  rw [← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [Polynomial.coeToPowerSeries.algHom_apply, Algebra.id.map_eq_id, Polynomial.coe_X,
    map_X]
  erw [AlgHom.comp_apply]
  simp only [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply,
    Algebra.id.map_eq_id, MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]
  rfl

/- example :(substAlgHom ha).comp
    ((MvPolynomial.coeToMvPowerSeries.algHom R).comp
      (Polynomial.aeval (MvPolynomial.X () : MvPolynomial Unit R)))
    = (Polynomial.aeval a) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X]
  erw [AlgHom.comp_apply]
  simp only [Polynomial.aeval_X, MvPolynomial.coeToMvPowerSeries.algHom_apply, Algebra.id.map_eq_id,
    MvPowerSeries.map_id, MvPolynomial.coe_X, RingHom.id_apply]
  -- we need substAlgHom_coe
  rw [← MvPolynomial.coe_X, substAlgHom]
  erw [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_coe, MvPolynomial.aeval_X]
-/

theorem subst_coe (p : Polynomial R) :
    subst (R := R) a (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [coe_subst ha, p.toPowerSeries_toMvPowerSeries, substAlgHom]
  erw [MvPowerSeries.substAlgHom_apply _]
  rw [MvPowerSeries.subst_coe ha.const, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp only [AlgHom.coe_comp, Function.comp_apply, Polynomial.aeval_X, MvPolynomial.aeval_X]

theorem subst_X :
    subst a (X : PowerSeries R) = a := by
  rw [← Polynomial.coe_X, subst_coe ha, Polynomial.aeval_X]

--#exit --TODO: remove
/-
theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] {ε : S →ₐ[R] T} :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_subst ha.const ε

theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_substAlgHom ha.const ε
-/

def SubstDomain.comp {a : PowerSeries S} (ha : SubstDomain a)
    {b : MvPowerSeries υ T} (hb : SubstDomain b):
    SubstDomain (substAlgHom hb a) where
  const_coeff := MvPowerSeries.IsNilpotent_subst hb.const (ha.const_coeff)

variable
    {υ : Type*} [DecidableEq υ] {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {a : PowerSeries S} (ha : SubstDomain a)
    {b : MvPowerSeries υ T} (hb : SubstDomain b)
    {a' : MvPowerSeries τ S} (ha' : SubstDomain a')
    {b' : τ → MvPowerSeries υ T} (hb' : MvPowerSeries.SubstDomain b')

theorem substAlgHom_comp_substAlgHom :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha)
      = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _

theorem substAlgHom_comp_substAlgHom_apply (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom  ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f

theorem subst_comp_subst :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  have h := substAlgHom_comp_substAlgHom (R := R) ha hb
  simp only [DFunLike.ext_iff, AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply] at h
  exact funext h

theorem subst_comp_subst_apply (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst (R := R) ha hb) f

end PowerSeries
