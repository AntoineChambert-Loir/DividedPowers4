/- ACL and MIdFF, Lean 2022 meeting at Icerm
! This file was ported from Lean 3 source module divided_powers.basic
-/

import DividedPowers.Basic

namespace DividedPowers

section DividedPowersMorphisms

/-- Compatibility of a ring morphism with dp-structures -/
def isDPMorphism {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  I.map f ≤ J ∧ ∀ (n : ℕ), ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)
#align divided_powers.is_pd_morphism DividedPowers.isDPMorphism

theorem isDPMorphism.comp {A B C : Type _} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
    {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hcomp : g.comp f = h) :
    isDPMorphism hJ hK g → isDPMorphism hI hJ f → isDPMorphism hI hK h := by
  intro hg hf; rw [← hcomp]
  constructor
  · apply le_trans _ hg.1
    rw [← Ideal.map_map]
    exact Ideal.map_mono hf.1
  · intro n a ha
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← hf.2 n a ha]
    rw [hg.2]
    apply hf.1
    exact Ideal.mem_map_of_mem f ha
#align divided_powers.is_pd_morphism.comp DividedPowers.isDPMorphism.comp

/-- The structure of a dp_morphism between rings endowed with dp-rings -/
@[ext]
structure dpMorphism {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J)
  extends RingHom A B where
  ideal_comp : I.map toRingHom ≤ J
  dpow_comp : ∀ (n : ℕ), ∀ a ∈ I, hJ.dpow n (toRingHom a) = toRingHom (hI.dpow n a)
#align divided_powers.pd_morphism DividedPowers.dpMorphism

instance dpMorphism.instFunLike {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) :
    FunLike (dpMorphism hI hJ) A B where
  coe h := h.toRingHom
  coe_injective' h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh' ; ext; rw [hh']
#align divided_powers.pd_morphism_fun_like DividedPowers.dpMorphism.instFunLike

def dpMorphism.isDPMorphism {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    {hI : DividedPowers I} {hJ : DividedPowers J} (f : dpMorphism hI hJ) :
    isDPMorphism hI hJ f.toRingHom :=
  ⟨f.ideal_comp, f.dpow_comp⟩
#align divided_powers.pd_morphism.is_pd_morphism DividedPowers.dpMorphism.isDPMorphism

-- Roby65, Proposition 2. (TODO: rename?)
/-- The ideal on which two divided power structures on two ideals coincide -/
def dpMorphismIdeal {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) {f : A →+* B} (hf : I.map f ≤ J) : Ideal A
    where
  carrier := {x ∈ I | ∀ n : ℕ, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    refine' ⟨I.add_mem hx.1 hy.1, _⟩
    intro n
    rw [hI.dpow_add _ hx.1 hy.1, map_sum,
      hJ.dpow_add _ (hf (Ideal.mem_map_of_mem f hx.1)) (hf (Ideal.mem_map_of_mem f hy.1))]
    apply congr_arg
    ext k
    rw [map_mul, hx.2 k, hy.2 (n - k)]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Submodule.zero_mem, map_zero, true_and]
    intro n
    induction' n with n
    · rw [hI.dpow_zero I.zero_mem, hJ.dpow_zero J.zero_mem, map_one]
    · rw [hI.dpow_eval_zero n.succ_ne_zero, hJ.dpow_eval_zero n.succ_ne_zero, map_zero]
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_sep_iff, SetLike.mem_coe] at hx ⊢
    refine' ⟨I.smul_mem r hx.1, _⟩
    intro n
    rw [smul_eq_mul, hI.dpow_smul _ hx.1, map_mul, map_mul, map_pow,
      hJ.dpow_smul _ (hf (Ideal.mem_map_of_mem f hx.1)), hx.2 n]
#align divided_powers.pd_morphism_ideal DividedPowers.dpMorphismIdeal

-- Roby65, Proposition 3.  (TODO: rename?)
/-- The dp morphism induced by a ring morphism, provided divided powers match on a generating set -/
def dpMorphismFromGens {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) {f : A →+* B} {S : Set A} (hS : I = Ideal.span S)
    (hf : I.map f ≤ J) (h : ∀ (n : ℕ), ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    dpMorphism hI hJ where
  toRingHom := f
  ideal_comp := hf
  dpow_comp n x hx :=
    by
    have hS' : S ⊆ dpMorphismIdeal hI hJ hf :=
      by
      intro y hy
      simp only [SetLike.mem_coe, dpMorphismIdeal, Submodule.mem_mk, Set.mem_sep_iff,
        SetLike.mem_coe]
      exact ⟨by rw [hS]; exact Ideal.subset_span hy, fun n => h n y hy⟩
    rw [← Ideal.span_le, ← hS] at hS'
    exact ((hS' hx).2 n).symm
#align divided_powers.pd_morphism_from_gens DividedPowers.dpMorphismFromGens

/-- Identity as a dp morphism -/
def dpMorphism.id {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I) : dpMorphism hI hI
    where
  toRingHom := RingHom.id A
  ideal_comp := by simp only [Ideal.map_id, le_refl]
  dpow_comp n a _ := by simp only [RingHom.id_apply]
#align divided_powers.pd_morphism.id DividedPowers.dpMorphism.id

instance {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I) :
    Inhabited (dpMorphism hI hI) :=
  ⟨dpMorphism.id hI⟩

theorem dpMorphismFromGens_coe {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A}
    (hI : DividedPowers I) {J : Ideal B} (hJ : DividedPowers J) {f : A →+* B} {S : Set A}
    (hS : I = Ideal.span S) (hf : I.map f ≤ J)
    (h : ∀ (n : ℕ), ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    (dpMorphismFromGens hI hJ hS hf h).toRingHom = f :=
  rfl
#align divided_powers.pd_morphism_from_gens_coe DividedPowers.dpMorphismFromGens_coe

/- lemma dp_morphism_from_gens_apply {A B : Type*} [comm_ring A] [comm_ring B] {I : ideal A}
  (hI : divided_powers I) {J : ideal B} (hJ : divided_powers J) {f : A →+* B} {S : set A}
  (hS : I = ideal.span S) (hf : I.map f ≤ J)
  (h : ∀ (n : ℕ) (x ∈ S), f (hI.dpow n x) = hJ.dpow n (f x)) (a : A) :
  (dp_morphism_from_gens hI hJ hS hf h) a = f a:=
rfl
-/

/-  -- Bizarre : This defines the identity as a dpMorphism, this is weird.

def dpMorphismOfLe {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I) {B : Type _}
    [CommSemiring B] {J : Ideal B} (_ : DividedPowers J) (_ : dpMorphism hI hI) {K : Ideal B}
    (_ : K ≤ J) : dpMorphism hI hI
    where
  toRingHom := RingHom.id A
  ideal_comp := by simp only [Ideal.map_id, le_refl]
  dpow_comp := by
    intro n a _
    simp only [RingHom.id_apply]
#align divided_powers.pd_morphism_of_le DividedPowers.dpMorphismOfLe

-/

-- Generalization
theorem isDPMorphism_on_span {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) {S : Set A} (hS : I = Ideal.span S)
    (hS' : ∀ s ∈ S, f s ∈ J) (hdp : ∀ (n : ℕ), ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    isDPMorphism hI hJ f := by
  suffices h : I.map f ≤ J by
    apply And.intro h
    let dp_f := dpMorphismFromGens hI hJ hS h hdp
    intro n a ha
    rw [← dpMorphismFromGens_coe hI hJ hS h hdp, dp_f.dpow_comp n a ha]
  rw [hS, Ideal.map_span, Ideal.span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has
#align divided_powers.is_pd_morphism_on_span DividedPowers.isDPMorphism_on_span

theorem dp_uniqueness {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) {S : Set A} (hS : I = Ideal.span S)
    (hS' : ∀ s ∈ S, f s ∈ J) (hdp : ∀ (n : ℕ), ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    ∀ (n), ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  (isDPMorphism_on_span hI hJ f hS hS' hdp).2
#align divided_powers.dp_uniqueness DividedPowers.dp_uniqueness

theorem isDPMorphism.of_comp {A B C : Type _} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
    {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hcomp : g.comp f = h) (sf : J = I.map f) :
    isDPMorphism hI hJ f → isDPMorphism hI hK h → isDPMorphism hJ hK g :=
  by
  intro hf hh
  apply isDPMorphism_on_span; exact sf
  rintro b ⟨a, ha, rfl⟩; rw [← RingHom.comp_apply]; rw [hcomp]
  apply hh.1; apply Ideal.mem_map_of_mem; exact ha
  rintro n b ⟨a, ha, rfl⟩
  rw [← RingHom.comp_apply, hcomp, hh.2 n a ha, ← hcomp, RingHom.comp_apply]
  rw [hf.2 n a ha]
#align divided_powers.is_pd_morphism.of_comp DividedPowers.isDPMorphism.of_comp

-- Roby65, corollary after proposition 3
/-- Uniqueness of a divided powers given its values on a generating set -/
theorem dp_uniqueness_self {A : Type _} [CommSemiring A] {I : Ideal A} (hI hI' : DividedPowers I)
    {S : Set A} (hS : I = Ideal.span S) (hdp : ∀ (n : ℕ), ∀ a ∈ S, hI.dpow n a = hI'.dpow n a) :
    hI' = hI := by
  ext n a
  by_cases ha : a ∈ I
  . refine' hI.dp_uniqueness hI' (RingHom.id A) hS _ _ n a ha
    . intro s hs
      simp only [RingHom.id_apply, hS]
      exact Ideal.subset_span hs
    . simpa only [RingHom.id_apply] using hdp
  · rw [hI.dpow_null ha, hI'.dpow_null ha]
#align divided_powers.dp_uniqueness_self DividedPowers.dp_uniqueness_self

-- For the moment, the notation does not work
-- notation `p(` A `,` I, `,` hI `)` →ₚ  `(` B `,` J, `,` hJ `)` := dp_morphism hI hJ
-- Also, we expect a `dp` subscript
-- TODO : identity (done), composition…
end DividedPowersMorphisms

end DividedPowers
