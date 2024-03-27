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

def SubstDomain.map {T : Type*} [CommRing T] [Algebra R T]
    (ε : S →ₐ[R] T)
    {a : σ → MvPowerSeries τ S} (ha : SubstDomain a) :
    SubstDomain (fun s ↦ MvPowerSeries.map τ ε.toRingHom (a s)) where
  const_coeff := sorry
  tendsto_zero := sorry


def substDomain [Fintype σ] {a : σ → MvPowerSeries τ S}
    (ha : ∀ s, constantCoeff τ S (a s) = 0) : SubstDomain a where
  const_coeff := fun s ↦ by rw [ha s]; exact IsNilpotent.zero
  tendsto_zero := by simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]

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

theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  := by
  apply MvPowerSeries.comp_aeval
  sorry

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

def SubstDomain.map {T : Type*} [CommRing T] [Algebra R T]
    (ε : S →ₐ[R] T)
    {a : MvPowerSeries τ S} (ha : SubstDomain a) :
    SubstDomain (MvPowerSeries.map τ ε.toRingHom a) where
  const_coeff := sorry

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

theorem subst_subst
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_substAlgHom ha.const ε

theorem comp_substAlgHom
    {T : Type*} [CommRing T] [Algebra R T] (ε : S →ₐ[R] T) :
    (MvPowerSeries.mapAlgHom τ ε).comp (substAlgHom ha) = substAlgHom (ha.map ε)  :=
  MvPowerSeries.comp_substAlgHom ha.const ε

end PowerSeries

section ExponentialPowerSeries

/- Works, but is not very nice to use -/
open PowerSeries

variable (R : Type*) [CommRing R] (f : PowerSeries R)

noncomputable def Dom : Ideal (MvPowerSeries (Fin 2) R) where
  carrier := setOf PowerSeries.SubstDomain
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

variable {R}

noncomputable def T (i : Fin 2) : Dom R :=
  ⟨(MvPowerSeries.X i : MvPowerSeries (Fin 2) R), by
    simp [Dom]
    exact { const_coeff := by simp only [MvPowerSeries.constantCoeff_X,  IsNilpotent.zero] } ⟩

#check T 0

#check PowerSeries.subst (T 0).val f
#check subst (T 0).val f

def IsExponential (f : PowerSeries R) :=
  subst (T 0 + T 1 : Dom R).val  f = (subst (T 0).val f) * (subst (T 1).val f)

example (f g : PowerSeries R) (hf : IsExponential f) (hg : IsExponential g) :
    IsExponential (f * g) := by
  simp only [IsExponential] at hf hg ⊢
  simp only [coe_subst (T 0).prop, coe_subst (T 1).prop, coe_subst (T 0 + T 1).prop] at hf hg ⊢
  simp only [map_mul, hf, hg]
  ring

noncomputable example : PowerSeries R := X

noncomputable example (r : R) : PowerSeries R := r • X
noncomputable example (f : PowerSeries R) (hf : IsExponential f) (r : R) :
    IsExponential (subst (r • X : PowerSeries R) f) := by
  simp only [IsExponential] at hf ⊢
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
