/-
Copyright (c) 2022 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DividedPowers.Basic

--In PR #22318

open Ideal

namespace DividedPowers

/-- Given divided power structures on the `A`-ideal `I` and the `B`-ideal `J`, a ring morphism
  `A → B` is a divided power morphism if it is compatible with these divided power structures. -/
def IsDPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  I.map f ≤ J ∧ ∀ {n : ℕ}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)

lemma isDPMorphism_iff {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) :
    IsDPMorphism hI hJ f ↔ I.map f ≤ J ∧ ∀ n ≠ 0, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) := by
  rw [IsDPMorphism, and_congr_right_iff]
  refine fun hIJ ↦ ⟨fun H n _ ↦ H, fun H n ↦ ?_⟩
  by_cases hn : n = 0
  · intro _ ha
    rw [hn, hI.dpow_zero ha, hJ.dpow_zero (hIJ (mem_map_of_mem f ha)), map_one]
  · exact H n hn

namespace IsDPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} {hI : DividedPowers I} {hJ : DividedPowers J} (hK : DividedPowers K)

theorem map_dpow {f : A →+* B} (hf : IsDPMorphism hI hJ f) {n : ℕ} {a : A} (ha : a ∈ I) :
    f (hI.dpow n a) = hJ.dpow n (f a) := (hf.2 a ha).symm

/- theorem comp' {f : A →+* B} {g : B →+* C} {h : A →+* C} (hcomp : g.comp f = h)
    (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) : IsDPMorphism hI hK h := by
  rw [← hcomp]
  constructor
  · apply le_trans _ hg.1
    rw [← map_map]
    exact map_mono hf.1
  · intro n a ha
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← hf.2 a ha, hg.2]
    exact hf.1 (mem_map_of_mem f ha) -/

theorem comp {f : A →+* B} {g : B →+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
    IsDPMorphism hI hK (g.comp f) := by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha ↦ ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha, hg.2]
  exact hf.1 (mem_map_of_mem f ha)

end IsDPMorphism

/-- A bundled divided power morphism between rings endowed with divided power structures. -/
@[ext]
structure DPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) extends RingHom A B where
  ideal_comp : I.map toRingHom ≤ J
  dpow_comp : ∀ {n : ℕ}, ∀ a ∈ I, hJ.dpow n (toRingHom a) = toRingHom (hI.dpow n a)

namespace DPMorphism

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)

instance instFunLike:
    FunLike (DPMorphism hI hJ) A B where
  coe h := h.toRingHom
  coe_injective' h h' hh' := by
    cases h; cases h'; congr
    dsimp at hh' ; ext; rw [hh']

instance coe_ringHom : CoeOut (DPMorphism hI hJ) (A →+* B) :=
  ⟨DPMorphism.toRingHom⟩

@[simp]
theorem coe_toRingHom {f : DPMorphism hI hJ} : ⇑(f : A →+* B) = f :=
  rfl

@[simp]
lemma toRingHom_apply {f : DPMorphism hI hJ} {a : A} :
  f.toRingHom a = f a := rfl

/- @[simp]
lemma toRingHom_eq_coe {f : DPMorphism hI hJ} :
  f.toRingHom = f := rfl -/

variable {hI hJ}

lemma isDPMorphism (f : DPMorphism hI hJ) : IsDPMorphism hI hJ f.toRingHom :=
  ⟨f.ideal_comp, f.dpow_comp⟩

def mk' {f : A →+* B} (hf : IsDPMorphism hI hJ f) : DPMorphism hI hJ :=
  ⟨f, hf.1, hf.2⟩

variable (hI hJ)

-- Roby65, Proposition 2.
/-- Given a ring homomorphism `A → B` and ideals `I ⊆ A` and `J ⊆ B` such that `I.map f ≤ J`,
  this is the `A`-ideal on which `f (hI.dpow n x) = hJ.dpow n (f x)`.-/
def ideal {f : A →+* B} (hf : I.map f ≤ J) : Ideal A where
  carrier  := {x ∈ I | ∀ n : ℕ, f (hI.dpow n (x : A)) = hJ.dpow n (f (x : A))}
  add_mem' := fun hx hy ↦ by
    simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
    refine ⟨I.add_mem hx.1 hy.1, fun n ↦ ?_⟩
    rw [hI.dpow_add hx.1 hy.1, map_sum,
      hJ.dpow_add (hf (mem_map_of_mem f hx.1)) (hf (mem_map_of_mem f hy.1))]
    apply congr_arg
    ext k
    rw [_root_.map_mul, hx.2, hy.2]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Submodule.zero_mem, map_zero, true_and]
    intro n
    induction n with
    | zero => rw [hI.dpow_zero I.zero_mem, hJ.dpow_zero J.zero_mem, map_one]
    | succ n => rw [hI.dpow_eval_zero n.succ_ne_zero, hJ.dpow_eval_zero n.succ_ne_zero, map_zero]
  smul_mem' := fun r x hx ↦ by
    simp only [Set.mem_sep_iff, SetLike.mem_coe] at hx ⊢
    refine ⟨I.smul_mem r hx.1, (fun n ↦ ?_)⟩
    rw [smul_eq_mul, hI.dpow_mul hx.1, _root_.map_mul, _root_.map_mul, map_pow,
      hJ.dpow_mul (hf (mem_map_of_mem f hx.1)), hx.2 n]

-- Roby65, Proposition 3.  (TODO: rename?)
/-- The dp morphism induced by a ring morphism, provided divided powers match on a generating set -/
def fromGens {f : A →+* B} {S : Set A} (hS : I = span S) (hf : I.map f ≤ J)
    (h : ∀ {n : ℕ}, ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) : DPMorphism hI hJ where
  toRingHom          := f
  ideal_comp         := hf
  dpow_comp {n} x hx := by
    have hS' : S ⊆ ideal hI hJ hf := fun y hy ↦ by
      simp only [SetLike.mem_coe, ideal, Submodule.mem_mk, Set.mem_sep_iff, SetLike.mem_coe]
      exact ⟨hS ▸ subset_span hy, fun n => h y hy⟩
    rw [← span_le, ← hS] at hS'
    exact ((hS' hx).2 n).symm

/-- Identity as a dp morphism -/
def id : DPMorphism hI hI where
  toRingHom     := RingHom.id A
  ideal_comp    := by simp only [map_id, le_refl]
  dpow_comp _ _ := by simp only [RingHom.id_apply]

instance : Inhabited (DPMorphism hI hI) := ⟨DPMorphism.id hI⟩

theorem fromGens_coe {f : A →+* B} {S : Set A} (hS : I = span S) (hf : I.map f ≤ J)
    (h : ∀ {n : ℕ}, ∀ x ∈ S, f (hI.dpow n x) = hJ.dpow n (f x)) :
    (fromGens hI hJ hS hf h).toRingHom = f := rfl

end DPMorphism

namespace IsDPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} (hI : DividedPowers I) (hJ : DividedPowers J) (hK : DividedPowers K)

open DPMorphism

-- Generalization
theorem on_span {f : A →+* B} {S : Set A} (hS : I = span S) (hS' : ∀ s ∈ S, f s ∈ J)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) : IsDPMorphism hI hJ f := by
  suffices h : I.map f ≤ J by
    exact ⟨h, fun a ha ↦ by
      rw [← fromGens_coe hI hJ hS h hdp, (fromGens hI hJ hS h hdp).dpow_comp a ha]⟩
  rw [hS, map_span, span_le]
  rintro b ⟨a, has, rfl⟩
  exact hS' a has

/-
theorem of_comp' (f : A →+* B) (g : B →+* C) (h : A →+* C) (hcomp : g.comp f = h)
    (heq : J = I.map f) (hf : IsDPMorphism hI hJ f) (hh : IsDPMorphism hI hK h) :
    IsDPMorphism hJ hK g := by
  apply on_span _ _ heq
  · rintro b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply, hcomp]
    exact hh.1 (mem_map_of_mem _ ha)
  · rintro n b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply, hcomp, hh.2 a ha, ← hcomp, RingHom.comp_apply, hf.2 a ha]-/

theorem of_comp (f : A →+* B) (g : B →+* C) -- (h : A →+* C) (hcomp : g.comp f = h)
    (heq : J = I.map f) (hf : IsDPMorphism hI hJ f) (hh : IsDPMorphism hI hK (g.comp f)) :
    IsDPMorphism hJ hK g := by
  apply on_span _ _ heq
  · rintro b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply]
    exact hh.1 (mem_map_of_mem _ ha)
  · rintro n b ⟨a, ha, rfl⟩
    rw [← RingHom.comp_apply, hh.2 a ha, RingHom.comp_apply, hf.2 a ha]

end IsDPMorphism

namespace DPMorphism

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] {I : Ideal A}
  {J : Ideal B} {K : Ideal C} {hI : DividedPowers I} {hJ : DividedPowers J} {hK : DividedPowers K}

protected def comp (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
    DPMorphism hI hK :=
  mk' (IsDPMorphism.comp hK g.isDPMorphism f.isDPMorphism)

@[simp]
lemma comp_toRingHom (g : DPMorphism hJ hK) (f : DPMorphism hI hJ) :
  (g.comp f).toRingHom = g.toRingHom.comp f.toRingHom := rfl


end DPMorphism

section Uniqueness

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI hI' : DividedPowers I) (hJ : DividedPowers J) {f : A →+* B}

theorem dpow_comp_from_gens {S : Set A} (hS : I = span S) (hS' : ∀ s ∈ S, f s ∈ J)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, f (hI.dpow n a) = hJ.dpow n (f a)) :
    ∀ {n}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  (IsDPMorphism.on_span hI hJ hS hS' hdp).2

-- Roby65, corollary after proposition 3
/-- Uniqueness of a divided powers given its values on a generating set -/
theorem dpow_eq_from_gens {S : Set A} (hS : I = span S)
    (hdp : ∀ {n : ℕ}, ∀ a ∈ S, hI.dpow n a = hI'.dpow n a) : hI' = hI := by
  ext n a
  by_cases ha : a ∈ I
  . refine hI.dpow_comp_from_gens hI' (f := RingHom.id A) hS ?_ ?_ a ha
    . intro s hs
      simp only [RingHom.id_apply, hS]
      exact subset_span hs
    . intro m b hb
      simpa only [RingHom.id_apply] using (hdp b hb)
  · rw [hI.dpow_null ha, hI'.dpow_null ha]

end Uniqueness

end DividedPowers
