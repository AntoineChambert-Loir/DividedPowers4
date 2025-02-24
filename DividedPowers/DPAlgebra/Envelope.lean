/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import DividedPowers.DPAlgebra.Compatible
import Mathlib.Data.Rel

universe u v w

open DividedPowerAlgebra DividedPowers Ideal

section IdealAdd

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v} [CommRing B]
  [Algebra A B] {J : Ideal B}

-- TODO: move to IdealAdd file
theorem IdealAdd.dividedPowers_dpow_eq_algebraMap (hJ : DividedPowers J)
    (hI' : DividedPowers (map (algebraMap A B) I))
    (hI'_ext : ∀ {n : ℕ} (a : A), hI'.dpow n ((algebraMap A B) a) = (algebraMap A B) (hI.dpow n a))
    (hI'_int : ∀ (n : ℕ), ∀ b ∈ J ⊓ map (algebraMap A B) I, hJ.dpow n b = hI'.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers hJ hI' hI'_int).dpow n ((algebraMap A B) a) =
      (algebraMap A B) (hI.dpow n a) := by
  rw [← hI'_ext]
  exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int (mem_map_of_mem (algebraMap A B) ha)

theorem IdealAdd.dividedPowers_dpow_eq_algebraMap' (hJ : DividedPowers J)
    (hI' : DividedPowers (map (algebraMap A B) I))
    (hI'_ext : hI.IsDPMorphism hI' (algebraMap A B))
    (h_int : ∀ (n : ℕ), ∀ b ∈ map (algebraMap A B) I ⊓ J, hI'.dpow n b = hJ.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers hI' hJ h_int).dpow n ((algebraMap A B) a) =
      (algebraMap A B) (hI.dpow n a) := by
  rw [← hI'_ext.2 _ ha]
  exact IdealAdd.dpow_eq_of_mem_left _ _ h_int (mem_map_of_mem (algebraMap A B) ha)

def IdealAdd.subDPIdeal_right {K : Ideal A} (hK : DividedPowers K)
    (hIK : ∀ (n : ℕ), ∀ a ∈ I ⊓ K, hI.dpow n a = hK.dpow n a) :
    SubDPIdeal (IdealAdd.dividedPowers hI hK hIK) where
  carrier           := K
  isSubideal c hc   := Ideal.mem_sup_right hc
  dpow_mem _ hn _ hj  := by
    rw [IdealAdd.dpow_eq_of_mem_right hI hK hIK hj]
    exact hK.dpow_mem hn hj

def IdealAdd.subDPIdeal_left {K : Ideal A} (hK : DividedPowers K)
    (hIK : ∀ (n : ℕ), ∀ a ∈ I ⊓ K, hI.dpow n a = hK.dpow n a) :
    SubDPIdeal (IdealAdd.dividedPowers hI hK hIK) where
  carrier           := I
  isSubideal c hc   := Ideal.mem_sup_left hc
  dpow_mem _ hn _ hj  := by
    rw [IdealAdd.dpow_eq_of_mem_left hI hK hIK hj]
    exact hI.dpow_mem hn hj


end IdealAdd

namespace DividedPowers

/-- The universal property of a divided power envelope

[Berthelot-Ogus], Theorem 3.19 (general case) -/
def IsDPEnvelope {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] [Algebra A B] (J : Ideal B) {D : Type v} [CommRing D] (J' : Ideal D)
    (hJ' : DividedPowers J') (ψ : B →+* D) (_ : J.map ψ ≤ J') : Prop :=
  ∀ (C : Type w) [CommRing C],
    ∀ [Algebra A C] [Algebra B C],
      ∀ [IsScalarTower A B C],
        ∀ (K : Ideal C) (hK : DividedPowers K)
          (_ : J.map (algebraMap B C) ≤ K)
          (_ : IsCompatibleWith hI hK (algebraMap A C)),
          ∃! φ : DPMorphism hJ' hK, φ.toRingHom.comp ψ = algebraMap B C

-- Note (ACL) : I add the assumption `I.map (algebraMap A B) ≤ J`, otherwise the property is not reasonable
/-- The weak divided powers envelope, under an additional condition

[Berthelot-Ogus], Theorem 3.19, case 1 -/
def IsWeakDPEnvelope {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] [Algebra A B] (J : Ideal B) (_ : I.map (algebraMap A B) ≤ J)
    {D : Type v} [CommRing D] (J' : Ideal D)
    (hJ' : DividedPowers J') (ψ : B →+* D) (_ : J.map ψ ≤ J') : Prop :=
  ∀ (C : Type w) [CommRing C],
    ∀ [Algebra A C] [Algebra B C],
      ∀ [IsScalarTower A B C],
        ∀ (K : Ideal C) (hK : DividedPowers K)
          (_ : J.map (algebraMap B C) ≤ K)
          (_ : I.map (algebraMap A C) ≤ K)
          (_ : IsCompatibleWith hI hK (algebraMap A C)),
          ∃! φ : DPMorphism hJ' hK, φ.toRingHom.comp ψ = algebraMap B C

-- TODO: universes?

namespace DividedPowerEnvelope

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v} [CommRing B]
  [Algebra A B] (J : Ideal B)

-- Case 1 of the proof, B-O pg 61 in pdf
-- 2.3 in B.
section Included

open DividedPowers DividedPowerAlgebra

-- We assume that `f(I) ⊆ J`. (`f = algebraMap A B`)
variable (hIJ : I.map (algebraMap A B) ≤ J)

include hIJ in
lemma algebraMap_dpow_mem (x : I) {n : ℕ} (hn : n ≠ 0) :
    algebraMap _ _ (algebraMap A B (dpow hI n x)) ∈ J := by
  apply hIJ
  simp only [Algebra.id.map_eq_id, RingHomCompTriple.comp_apply]
  exact Ideal.mem_map_of_mem _ (dpow_mem _ hn x.2)

-- (DividedPowerAlgebra.ι B J x) is the map φ in B-O
-- (i)
/-- The generators of the first kind for the suitable ideal of the divided power algebra

[Berthelot-Ogus], page 61, (i) -/
inductive rel1 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : J} : rel1 (ι B J x) (algebraMap _ _ (x : B))

variable {J} in
lemma rel1_apply (x : J) :
  rel1 J ((ι B ↥J) x) ((algebraMap B (DividedPowerAlgebra B ↥J)) ↑x) := by constructor

-- J1
/-- The ideal of the divided power algebra generated by the generators of the first kind

[Berthelot-Ogus], page 61, 𝒥₁ -/
noncomputable def J1 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel1 J)

variable {J} in
lemma rel1_mem_J1 (x : J) :
    ((ι B ↥J) x - ((algebraMap B (DividedPowerAlgebra B ↥J)) ↑x)) ∈ J1 J := by
  apply subset_span
  use (ι B ↥J) x, (algebraMap B (DividedPowerAlgebra B ↥J)) ↑x
  constructor
  · exact rel1_apply x
  simp only [sub_add_cancel]


-- (ii)
/- inductive rel2 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2 (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (algebraMap _ _ (algebraMap A B (dpow hI n x))) -/

-- (ii)'
/-- The generators of the second kind of the suitable ideal of the divided power algebra

[Berthelot-Ogus], page 61, (ii)' -/
inductive rel2' : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2' (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap A B (dpow hI n x)), algebraMap_dpow_mem hI J hIJ x hn⟩)

variable {J} in
lemma rel2'_apply {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2' hI J hIJ (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap A B (dpow hI n x)), algebraMap_dpow_mem hI J hIJ x hn⟩) :=
  rel2'.Rel hn

-- J2
/-- The ideal of the divided power algebra generated by the generators of the first kind

[Berthelot-Ogus], page 61, 𝒥₂ -/
noncomputable def J2 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel2' hI J hIJ)

lemma rel2'_mem_J2 (x : I) {n : ℕ} (hn : n ≠ 0) :
    (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J)) -
      (ι B J ⟨(algebraMap A B (dpow hI n x)), algebraMap_dpow_mem hI J hIJ x hn⟩) ∈
        J2 hI J hIJ := by
  apply subset_span
  use (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J)),
      (ι B J ⟨(algebraMap A B (dpow hI n x)), algebraMap_dpow_mem hI J hIJ x hn⟩)
  simp [sub_add_cancel, rel2'_apply hI hIJ hn]


/-- The suitable ideal of the divided power algebra

[Berthelot-Ogus], page 61, 𝒥 -/
noncomputable def J12 : Ideal (DividedPowerAlgebra B J) :=
  J1 J + J2 hI J hIJ

-- TODO: we might need something similar for rel2
lemma rel1_mem_J12 (x : J) :
    ((ι B ↥J) x - ((algebraMap B (DividedPowerAlgebra B ↥J)) ↑x)) ∈ J12 hI J hIJ :=
  mem_sup_left (rel1_mem_J1 x)

private theorem sub_add_sub {A : Type*} [AddCommGroup A] (a b c d : A) :
    (a - b) + (c - d) = a - d + (c - b) := by abel

lemma rel2_mem_J12 (x : I) {n : ℕ} (hn : n ≠ 0) :
    (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J)) -
      algebraMap _ _ (algebraMap A B (dpow hI n x)) ∈ J12 hI J hIJ := by
  have h := rel1_mem_J12 hI J hIJ (⟨algebraMap A B (dpow hI n x),
        hIJ (Ideal.mem_map_of_mem (algebraMap A B) (hI.dpow_mem hn x.prop))⟩ : J)
  rw [← Ideal.neg_mem_iff, neg_sub] at h
  rw [← Ideal.add_mem_iff_left (J12 hI J hIJ) h, sub_add_sub]
  apply Ideal.add_mem _ (mem_sup_right (rel2'_mem_J2 hI J hIJ x hn))
  simp only [sub_self, Submodule.zero_mem]


  /- inductive rel2' : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2' (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap _ _ (algebraMap A B (dpow hI n x))), algebraMap_dpow_mem hI J hIJ x hn⟩)-/

-- B-O : Claim in pg 61, proof in pg 62
theorem J12_IsSubDPIdeal [DecidableEq B] :
    IsSubDPIdeal (DividedPowerAlgebra.dividedPowers' B J)
      (J12 hI J hIJ ⊓ DividedPowerAlgebra.augIdeal B J) where
  isSubideal := inf_le_right
  dpow_mem   := fun _ hn x hx ↦ by
    have hJ12 : J12 hI J hIJ ⊓ augIdeal B J = (J1 J  ⊓ augIdeal B J) + J2 hI J hIJ := sorry
    --simp only [dividedPowers', Subtype.forall, mem_inf]
    rw [hJ12, Submodule.add_eq_sup, Submodule.mem_sup'] at hx
    obtain ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩, hx⟩ := hx
    suffices ∀ n (hn : n ≠ 0),
        ((dividedPowers' B ↥J).dpow n x1 ∈ J12 hI J hIJ ⊓ augIdeal B ↥J ∧
        (dividedPowers' B ↥J).dpow n x2 ∈ J12 hI J hIJ ⊓ augIdeal B ↥J) by
      sorry
    intro n hn
    constructor
    · have heq : J1 J ⊓ augIdeal B ↥J = J1 J * augIdeal B ↥J := by
        apply le_antisymm _ Ideal.mul_le_inf
        sorry
      have hsub : IsSubDPIdeal (DividedPowerAlgebra.dividedPowers' B J)
        (J1 J * augIdeal B ↥J) := {
          isSubideal := mul_le_left
          dpow_mem   := fun n hn x hx ↦ by
            --simp? [Ideal.mul_le_inf] at hx
            sorry
        }
      have hss : J1 J * augIdeal B ↥J ≤ J12 hI J hIJ ⊓ augIdeal B ↥J :=
        heq ▸ inf_le_inf_right (augIdeal B ↥J) le_sup_left
      rw [heq] at hx1
      exact hss (hsub.dpow_mem n hn hx1)
    · sorry/- revert n
      induction x2 using DividedPowerAlgebra.induction_on with
      | h_C b =>
          intro n hn
          rw [mk_C]
          sorry
      | h_add a b hna hnb =>
          intro n hn
          rw [dpow_add]
          sorry
      | h_dp x m a hnx =>
          intro n hn
          sorry  -/

/-- The weak divided power envelope of an ideal, in the particular case

[Berthelot-Ogus], page 62, 𝒟 -/
def dpEnvelopeOfIncluded : Type v :=
  DividedPowerAlgebra B J ⧸ J12 hI J hIJ

noncomputable instance : CommRing (dpEnvelopeOfIncluded hI J hIJ) :=
  Quotient.commRing (J12 hI J hIJ)
  --Ideal.Quotient.commRing _

noncomputable instance : Algebra B (dpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.algebra _

noncomputable instance algebraOfIncluded : Algebra A (dpEnvelopeOfIncluded hI J hIJ) :=
  ((algebraMap B (dpEnvelopeOfIncluded hI J hIJ)).comp (algebraMap A B)).toAlgebra

noncomputable instance algebraOfIncluded'' :
    Algebra (DividedPowerAlgebra B J) (dpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.algebra _

instance isScalarTower_of_included : IsScalarTower A B (dpEnvelopeOfIncluded hI J hIJ) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

/-- The divided power ideal in the weak divided power envelope

[Berthelot-Ogus], page 62, J_bar -/
noncomputable def dpIdealOfIncluded [DecidableEq B] : Ideal (dpEnvelopeOfIncluded hI J hIJ) :=
  map (Ideal.Quotient.mk (J12 hI J hIJ)) (DividedPowerAlgebra.augIdeal B J)

set_option pp.instances true
-- J_bar has DP
theorem sub_ideal_dpIdealOfIncluded [DecidableEq B] :
    J.map (algebraMap B (dpEnvelopeOfIncluded hI J hIJ)) ≤ dpIdealOfIncluded hI J hIJ := by
  have heq : algebraMap B (dpEnvelopeOfIncluded hI J hIJ) =
    (algebraMap (DividedPowerAlgebra B J) (dpEnvelopeOfIncluded hI J hIJ)).comp
      (algebraMap B (DividedPowerAlgebra B J)) := rfl
  intro x hx
  rw [dpIdealOfIncluded, Ideal.mem_map_iff_of_surjective _ Quotient.mk_surjective]
  rw [heq, ← map_map, mem_map_iff_of_surjective] at hx
  obtain ⟨y, hyJ, hyx⟩ := hx
  · rw [← hyx]
    rw [map, ← submodule_span_eq] at hyJ
    --TODO:lemma
    have hmap : algebraMap (DividedPowerAlgebra B ↥J) (dpEnvelopeOfIncluded hI J hIJ) =
      Ideal.Quotient.mk (J12 hI J hIJ) := rfl
    simp_rw [hmap]
    suffices y ∈ (augIdeal B J) ⊔ (J12 hI J hIJ) by
      rw [Submodule.mem_sup] at this
      obtain ⟨y, hy, z, hz, rfl⟩ := this
      use y, hy
      unfold dpEnvelopeOfIncluded
      rw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem (y + z) y]
      simp only [add_sub_cancel_left, hz]
    apply Submodule.span_induction (p := fun y _ ↦ y ∈ (augIdeal B J) ⊔ (J12 hI J hIJ))
      _ _ _ _ hyJ
    · intro x hx
      simp only [Set.mem_image, SetLike.mem_coe] at hx
      obtain ⟨y, hyJ, hyx⟩ := hx
      have hsub : (((algebraMap B (DividedPowerAlgebra B ↥J)) y) - (ι B ↥J) ⟨y, hyJ⟩) ∈
          J12 hI J hIJ := by
        rw [← neg_sub, Ideal.neg_mem_iff]
        exact rel1_mem_J12 hI J hIJ ⟨y, hyJ⟩
      rw [Submodule.mem_sup]
      use ((ι B ↥J) ⟨y, hyJ⟩), dp_mem_augIdeal B ↥J zero_lt_one ⟨y, hyJ⟩,
        (((algebraMap B (DividedPowerAlgebra B ↥J)) y) - (ι B ↥J) ⟨y, hyJ⟩), hsub
      rw [← hyx]
      ring
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      simp only [Submodule.mem_sup] at hx hy ⊢
      obtain ⟨ax, hax, cx, hcx, hx⟩ := hx
      obtain ⟨ay, hay, cy, hcy, hy⟩ := hy
      use (ax + ay), Ideal.add_mem _ hax hay, (cx + cy), Ideal.add_mem _ hcx hcy
      simp only [← hx, ← hy]
      ring
    · intro a x _ hx
      simp only [Submodule.mem_sup] at hx ⊢
      obtain ⟨bx, hbx, cx, hcx, hx⟩ := hx
      use a • bx, Submodule.smul_mem _ a hbx, a • cx, Submodule.smul_mem _ a hcx
      rw [← hx, smul_add]
  exact Quotient.mk_surjective

-- Second part of Theorem 3.19
lemma isCompatibleWith_of_included [DecidableEq B]
    [∀ x, Decidable (x ∈ (dpIdealOfIncluded hI J hIJ).carrier)] :
    IsCompatibleWith hI (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J)
      (J12_IsSubDPIdeal hI J hIJ)) (algebraMap A (dpEnvelopeOfIncluded hI J hIJ)) := by
  set hJ := (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J)
      (J12_IsSubDPIdeal hI J hIJ))
  --have hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a := sorry
  --have := (IsCompatibleWith_tfae hI hJ (algebraMap A (dpEnvelopeOfIncluded hI J hIJ))).out 0 1
  --rw [← extends_to_def, extends_to_iff_exists_dpIdeal] at this
  rw [IsCompatibleWith]
  have I' := I.map (algebraMap A (dpEnvelopeOfIncluded hI J hIJ))
  have J' := (augIdeal B J).map (Ideal.Quotient.mk (J12 hI J hIJ))

  have : extends_to hI (algebraMap A (dpEnvelopeOfIncluded hI J hIJ)) := by
    rw [extends_to_iff_exists_dpIdeal]
    use dpIdealOfIncluded hI J hIJ
    use (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J)
      (J12_IsSubDPIdeal hI J hIJ))
    rw [IsDPMorphism]
    constructor
    · apply le_trans _ (sub_ideal_dpIdealOfIncluded _ _ _)
      have hmap : (algebraMap A (dpEnvelopeOfIncluded hI J hIJ)) =
        (algebraMap B (dpEnvelopeOfIncluded hI J hIJ)).comp (algebraMap A B) := rfl
      rw [hmap]
      simp only [← map_map]
      apply map_mono hIJ
    · intro n a haI
      rw [Quotient.dividedPowers]
      --rw [Quotient.OfSurjective.dpow_apply]


      sorry

  obtain ⟨hI', h⟩ := this

  use hI', h
  rintro n b ⟨hb, hb'⟩
  simp only [SetLike.mem_coe] at hb hb'
  rw [IsDPMorphism] at h
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hb'
  · rintro x ⟨a, haI, rfl⟩
    --erw [h.2 a haI]
    sorry
  · sorry
  · sorry
  · sorry

  /- have hsurj : Function.Surjective ⇑(Ideal.Quotient.mk (J12 hI J hIJ)) := by
    apply Ideal.Quotient.mk_surjective
  have := Ideal.mem_image_of_mem_map_of_surjective _ hsurj hb
  obtain ⟨c, hc, rfl⟩ := this -/

  /- have hmap :  (algebraMap A (dpEnvelopeOfIncluded hI J hIJ))  =
    (Ideal.Quotient.mk (J12 hI J hIJ)) := sorry
  rw [h.2] -/
    --((Ideal.Quotient.mk (J12 hI J hIJ)) (augIdeal B ↥J))

  --sorry

  /- set hK : DividedPowers (map (algebraMap A _) I +
      map (Ideal.Quotient.mk (J12 hI J hIJ)) (augIdeal B ↥J)) := by
    apply IdealAdd.dividedPowers hI' (Quotient.dividedPowers
      (DividedPowerAlgebra.dividedPowers' B J) (J12_IsSubDPIdeal hI hIJ))

    sorry
    with hK_def -/
  --use IdealAdd.dividedPowers hI hJ (by sorry)
 /-  use hK
  constructor
  · simp only [IsDPMorphism, Submodule.add_eq_sup, le_sup_left, true_and]
    intro n a haI
    rw [hK_def]
    --rw [IdealAdd.dpow_eq_of_mem_left]
    --rw [IdealAdd.dividedPowers_dpow_eq_algebraMap]
    sorry
  · simp only [IsDPMorphism, map_id, Submodule.add_eq_sup, le_sup_right, RingHom.id_apply,
    true_and]
    sorry -/


-- End of case 1
theorem dpEnvelopeOfIncluded_IsWeakDPEnvelope [DecidableEq B] :
    IsWeakDPEnvelope hI J hIJ (dpIdealOfIncluded hI J hIJ)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J) (J12_IsSubDPIdeal hI J hIJ))
      (algebraMap B (dpEnvelopeOfIncluded hI J hIJ)) (sub_ideal_dpIdealOfIncluded hI J hIJ) := by
  rw [IsWeakDPEnvelope]
  intro C _ _ _ _ K hK hJK hIK hcomp
  simp only [IsCompatibleWith, mem_inf, and_imp] at hcomp
  have hAC : hI.IsDPMorphism hK (algebraMap A C) := {
    left  := hIK
    right := by
      obtain ⟨hI', h, hh⟩ := hcomp
      intro n a haI
      rw [← hh n ((algebraMap A C) a) (mem_map_of_mem (algebraMap A C) haI), h.2 a haI]
      exact (hIK (mem_map_of_mem (algebraMap A C) haI)) -- Q : Why does this appear??
  }
  have hDC : (DividedPowerAlgebra.dividedPowers' B J).IsDPMorphism hK (sorry) := sorry

  sorry

end Included

-- 2.4 in B. (with compatibility property)
section General

variable (I)

/-- The modified ideal to build the divided power envelope

[Berthelot-Ogus], page 62, J1 -/
def J' : Ideal B :=
  J + I.map (algebraMap A B)

-- IB is a subideal of J'
theorem sub_ideal_J' : I.map (algebraMap A B) ≤ J' I J :=
  le_sup_of_le_right (le_refl _)

variable {I}

/-- The divided power envelope of an ideal

[Berthelot-Ogus], page 61, 𝒟_B,γ(J₁) -/
def dpEnvelope : Type v :=
  dpEnvelopeOfIncluded hI (J' I J) (sub_ideal_J' I J)
--  DividedPowerAlgebra B (J' I J) ⧸ J12 hI (J' I J) (sub_ideal_J' I J)

noncomputable instance : CommRing (dpEnvelope hI J) :=
  Ideal.Quotient.commRing (J12 hI (J' I J) (sub_ideal_J' I J))

noncomputable instance : Algebra B (dpEnvelope hI J) :=
  Ideal.Quotient.algebra B

lemma algebraMap_eq : algebraMap B (dpEnvelope hI J) =
    (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))).comp
      (algebraMap B (DividedPowerAlgebra B (J' I J))) := rfl

noncomputable instance algebra' : Algebra A (dpEnvelope hI J) :=
  ((algebraMap B (dpEnvelope hI J)).comp (algebraMap A B)).toAlgebra

noncomputable instance algebra'' : Algebra (DividedPowerAlgebra B (J' I J)) (dpEnvelope hI J) :=
  Ideal.Quotient.algebra _

instance : IsScalarTower A B (dpEnvelope hI J) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

lemma dpEnvelope_eq_dpEnvelopeOfIncluded (hIJ : map (algebraMap A B) I ≤ J) :
    dpEnvelope hI J = dpEnvelopeOfIncluded hI J hIJ := by
  have hJ : J' I J = J := by
    rw [J']
    exact LE.le.add_eq_left hIJ
  rw [dpEnvelope, dpEnvelopeOfIncluded]
  congr 2
  all_goals
    try rw [hJ]
  · exact heq_of_eqRec_eq (congrArg (LE.le (map (algebraMap A B) I)) hJ) rfl

section DecidableEq

variable [DecidableEq B]

/-- The modified divided power ideal of the divided power envelope

[Berthelot-Ogus], page 63, J₁_bar -/
noncomputable def J₁_bar : Ideal (dpEnvelope hI J) :=
  dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J)

/-- The divided power structure on the modified divided power ideal of the divided power envelope -/
noncomputable def dividedPowers' : DividedPowers (J₁_bar hI J) :=
  Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
    (J12_IsSubDPIdeal hI _ (sub_ideal_J' I J))

/-
lemma J_le_augIdeal :
    J.map (algebraMap B (DividedPowerAlgebra B (J' I J))) ≤ (augIdeal B ↥(J' I J)) := sorry

noncomputable def dpIdeal' : (dividedPowers' B ↥(J' I J)).SubDPIdeal :=
  SubDPIdeal.generatedDpow (DividedPowerAlgebra.dividedPowers' B (J' I J)) (J_le_augIdeal J) -/


lemma J_le_J₁_bar : map (algebraMap B (dpEnvelope hI J)) J ≤ J₁_bar hI J :=
  le_trans (map_mono (le_sup_of_le_left (le_refl J)))
    (sub_ideal_dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J))

/-- The divided power ideal of the divided power envelope

[Berthelot-Ogus], page 63, J_bar -/
noncomputable def dpIdeal : (dividedPowers' hI J).SubDPIdeal :=
  SubDPIdeal.generatedDpow (dividedPowers' hI J) (J_le_J₁_bar hI J)

-- First claim in Theorem 3.19 : `J⬝D_{B, γ} ⊆ J_bar`.
theorem sub_ideal_dpIdeal :
    J.map (algebraMap B (dpEnvelope hI J)) ≤ (dpIdeal hI J).carrier := by
  rw [dpIdeal, SubDPIdeal.generatedDpow_carrier]
  intros x hx
  apply subset_span
  use 1, one_ne_zero, x, hx, (dpow_one _ (J_le_J₁_bar _ _ hx)).symm

/-- The divided power structure on the divided power envelope -/
noncomputable def dividedPowers [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    DividedPowers (dpIdeal hI J).carrier :=
  IsSubDPIdeal.dividedPowers (dividedPowers' hI J) (dpIdeal hI J).toIsSubDPIdeal

-- Second part of Theorem 3.19
lemma isCompatibleWith [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    IsCompatibleWith hI (dividedPowers hI J) (algebraMap A (dpEnvelope hI J)) := by
  rw [IsCompatibleWith]
  -- hI' should be the restriction to this SubDPIdeal
  sorry

end DecidableEq
section

-- TODO: improve proof
lemma map_generatedDpow_le {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}
    {hI : DividedPowers I} {J : Ideal B} {hJ : DividedPowers J}
    (φ : DPMorphism hI hJ) {s : Set A} (hs : s ⊆ I)  :
    (SubDPIdeal.generatedDpow hI hs).carrier.map φ.toRingHom ≤ J := by
  simp only [SubDPIdeal.generatedDpow_carrier, map_span, span_le]
  rintro _ ⟨_, ⟨⟨n, hn, x, hx, rfl⟩, rfl⟩⟩
  rw [← φ.dpow_comp (n := n) x (hs hx)]
  exact hJ.dpow_mem hn (φ.ideal_comp (Ideal.mem_map_of_mem _ (hs hx)))

lemma map_generatedDpow_le_of_subDPIdeal {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}
    {hI : DividedPowers I} {J : Ideal B} {hJ : DividedPowers J} {J' : SubDPIdeal hJ}
    {φ : DPMorphism hI hJ} {s : Set A} (hs : s ⊆ I) (hφs : φ '' s ⊆ J') :
    (SubDPIdeal.generatedDpow hI hs).carrier.map φ.toRingHom ≤ J'.carrier := by
  simp only [SubDPIdeal.generatedDpow_carrier, map_span, span_le]
  rintro _ ⟨_, ⟨⟨n, hn, x, hx, rfl⟩, rfl⟩⟩
  rw [← φ.dpow_comp (n := n) x (hs hx)]
  exact J'.dpow_mem _ hn (φ x) (hφs (Set.mem_image_of_mem (⇑φ) hx))

-- Needed because `DPEnvelope` and `DPEnvelopeOfIncluded` are not the same type.
variable {hI J} in
theorem mem_dpIdealOfIncluded_of_mem_dpIdeal [DecidableEq B] {a : dpEnvelope hI J}
    (ha : a ∈ (dpIdeal hI J)) : a ∈ dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J) :=
  map_generatedDpow_le (DPMorphism.id (dividedPowers' hI J) ) (J_le_J₁_bar hI J)
    (Ideal.mem_map_of_mem _ ha)

section dpEnvelope_IsDPEnvelope

variable {C : Type*} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  (K : Ideal C) (hK : DividedPowers K) (hJK : map (algebraMap B C) J ≤ K)
  (hI' : DividedPowers (map (algebraMap A C) I)) (hI'_ext : hI.IsDPMorphism hI' (algebraMap A C))
  (hI'_int : ∀ (n : ℕ), ∀ b ∈ map (algebraMap A C) I ⊓ K, hI'.dpow n b = hK.dpow n b)

variable (I)

-- K1 in page 63 of B-O
private abbrev K1 : Ideal C := I.map (algebraMap A C) + K

variable {I K}

-- δ' in page 63 of B-O
private noncomputable abbrev h1 :  DividedPowers (K1 I K) := IdealAdd.dividedPowers hI' hK hI'_int

private lemma h1_def : h1 hK hI' hI'_int = IdealAdd.dividedPowers hI' hK hI'_int := rfl

-- Q: generalize and PR? (I.map (f : A →+* C)) + K, plus do left and right versions
private abbrev g' : hI.DPMorphism (h1 hK hI' hI'_int) :=
  { toRingHom  := algebraMap A C
    ideal_comp := le_sup_of_le_left (le_refl _)
    dpow_comp  := fun _ ha =>
      IdealAdd.dividedPowers_dpow_eq_algebraMap' hI hK hI' hI'_ext hI'_int _ _ ha }

private lemma algebraMap_J'_le_K1 (hJK : map (algebraMap B C) J ≤ K) :
    (J' I J).map (algebraMap B C) ≤ K1 I K := by
  rw [J', Ideal.add_eq_sup, Ideal.map_sup, sup_le_iff]
  refine ⟨le_trans hJK (le_sup_of_le_right (le_refl _)), ?_⟩
  rw [Ideal.map_map, Eq.symm (IsScalarTower.algebraMap_eq A B C)]
  exact le_sup_of_le_left (le_refl _)

private lemma isCompatibleWith_hI_h1 (hI'_ext : hI.IsDPMorphism hI' (algebraMap A C)) :
    IsCompatibleWith hI (h1 hK hI' hI'_int) (algebraMap A C) := by
  rw [IsCompatibleWith]
  use hI', hI'_ext
  intro n c hc
  exact (IdealAdd.dpow_eq_of_mem_left _ _ hI'_int hc.1).symm

-- TODO?: generalize to subpdideals of sums (left and right)
private abbrev K' : SubDPIdeal (h1 hK hI' hI'_int) :=
  { carrier := K
    isSubideal := le_sup_right
    dpow_mem := fun {n} hn j hj ↦ by
      suffices (h1 hK hI' hI'_int).dpow n j = hK.dpow n j by
        rw [this]
        apply hK.dpow_mem hn hj
      exact IdealAdd.dpow_eq_of_mem_right hI' hK hI'_int hj }

-- Not needed.
private lemma algebraMap_I_le_K1  :
    map (algebraMap A C) I ≤ K1 I K :=
  SemilatticeSup.le_sup_left _ _

private noncomputable abbrev φ [DecidableEq B] :
    (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B (J' I J))
      (J12_IsSubDPIdeal hI _ (sub_ideal_J' I J))).DPMorphism (h1 hK hI' hI'_int) :=
  (dpEnvelopeOfIncluded_IsWeakDPEnvelope hI (J' I J) (sub_ideal_J' I J) C _ (h1 hK hI' hI'_int)
    (algebraMap_J'_le_K1 J hJK) (SemilatticeSup.le_sup_left _ _)
    (isCompatibleWith_hI_h1 hI hK hI' hI'_int hI'_ext)).choose

private lemma hφ [DecidableEq B] : (φ hI J hK hJK hI' hI'_ext hI'_int).comp
    (algebraMap B (dpEnvelopeOfIncluded hI (J' I J) (sub_ideal_J' I J))) = algebraMap B C :=
  (dpEnvelopeOfIncluded_IsWeakDPEnvelope hI (J' I J) (sub_ideal_J' I J) C _ (h1 hK hI' hI'_int)
    (algebraMap_J'_le_K1 J hJK) (SemilatticeSup.le_sup_left _ _)
    (isCompatibleWith_hI_h1 hI hK hI' hI'_int hI'_ext)).choose_spec.1

private lemma hφ_unique  [DecidableEq B] :
    ∀ (y : (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
      (J12_IsSubDPIdeal hI _ (sub_ideal_J' I J))).DPMorphism (h1 hK hI' hI'_int)),
      (fun φ ↦ φ.comp (algebraMap B (dpEnvelopeOfIncluded hI (J' I J) (sub_ideal_J' I J))) =
        algebraMap B C) y → y = φ hI J hK hJK hI' hI'_ext hI'_int :=
  (dpEnvelopeOfIncluded_IsWeakDPEnvelope hI (J' I J) (sub_ideal_J' I J) C _ (h1 hK hI' hI'_int)
    (algebraMap_J'_le_K1 J hJK) (SemilatticeSup.le_sup_left _ _)
    (isCompatibleWith_hI_h1 hI hK hI' hI'_int hI'_ext)).choose_spec.2

private noncomputable abbrev ψ [DecidableEq B] [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    (dividedPowers hI J).DPMorphism hK where
  toRingHom  := (φ hI J hK hJK hI' hI'_ext hI'_int).toRingHom
  ideal_comp := by
    have hK' : (K : Ideal C) = (K' hK hI' hI'_int).carrier := rfl
    conv_rhs => rw [hK']
    rw [dpIdeal]
    apply map_generatedDpow_le_of_subDPIdeal
    suffices (map (algebraMap B (dpEnvelope hI J)) J).map
        (φ hI J hK hJK hI' hI'_ext hI'_int).toRingHom ≤ K' hK hI' hI'_int by
      rwa [Ideal.map, span_le] at this
    rw [Ideal.map_map, Ideal.map, span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [dpEnvelope, hφ hI J hK hJK hI' hI'_ext hI'_int, SetLike.mem_coe]
    exact le_trans hJK (le_refl K) (mem_map_of_mem (algebraMap B C) hb)
  dpow_comp  := fun {n} a ha => by
    -- On `K`, `h1.dpow` coincides with `hK.dpow`, by `dpow_eq_of_mem_right`
    -- The left hand side applies to `φ a`, so `hK` can be changed to `h1`
    rw [← IdealAdd.dpow_eq_of_mem_right hI' hK hI'_int]
    · have hφ_comp : ∀ a ∈ dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J),
          (h1 hK hI' hI'_int).dpow n (φ hI J hK hJK hI' hI'_ext hI'_int a) =
            φ hI J hK hJK hI' hI'_ext hI'_int _ :=
        (φ hI J hK hJK hI' hI'_ext hI'_int).dpow_comp (n := n)
      have ha' : a ∈ dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J) :=
        mem_dpIdealOfIncluded_of_mem_dpIdeal ha
      -- Then we apply `φ.dpow_comp`
      simp only [dpEnvelope, dpEnvelopeOfIncluded, DPMorphism.toRingHom_apply]
      rw [hφ_comp a ha']
      -- Get `dpow` for `dpEnvelopeOfIncluded`, for `J' I J`,
      -- but this will be the same as `dpow` for `dpEnvelope` because the element is there.
      rw [dividedPowers, IsSubDPIdeal.dpow_eq, if_pos ha]
      rfl
    · -- φ.toRingHom a ∈ K
      set K' : SubDPIdeal (h1 hK hI' hI'_int) := IdealAdd.subDPIdeal_right hI' hK hI'_int
      have hK' : K'.toIdeal = K := rfl
      have hK'_set : (K' : Set C) = K := rfl
      suffices _ ∈ K'.toIdeal by
        rw [hK'] at this
        exact this
      simp only [dpIdeal, SubDPIdeal.memCarrier] at ha
      have hφ' : ⇑(φ hI J hK hJK hI' hI'_ext hI'_int) ''
          (map (algebraMap B (dpEnvelope hI J)) J : Set (dpEnvelope hI J)) ⊆ K' := by
        unfold dpEnvelope dpEnvelopeOfIncluded
        simp only [Set.image_subset_iff]
        rw [← DPMorphism.coe_toRingHom, hK'_set,
          ← coe_comap (f := (φ hI J hK hJK hI' hI'_ext hI'_int).toRingHom) K]
        norm_cast
        rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
        have hφ_unf := hφ hI J hK hJK hI' hI'_ext hI'_int
        unfold dpEnvelopeOfIncluded at hφ_unf
        rw [hφ_unf]
        exact fun _ hx ↦ hJK (Ideal.mem_map_of_mem _ hx)
      exact map_generatedDpow_le_of_subDPIdeal (J_le_J₁_bar hI J) hφ' (Ideal.mem_map_of_mem _ ha)

private noncomputable def foo [DecidableEq B] :
    (DividedPowerAlgebra.dividedPowers' B ↥(J' I J)).DPMorphism (dividedPowers' hI J)  :=
  DPMorphism.mk' _ _ (Quotient.isDPMorphism (DividedPowerAlgebra.dividedPowers' B ↥(J' I J)) _)

private noncomputable def bar [DecidableEq B] [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    (dividedPowers hI J).DPMorphism (dividedPowers' hI J) :=
  DPMorphism.mk' _ _ (IsSubDPIdeal.isDPMorphism (dividedPowers' hI J) (dpIdeal hI J).toIsSubDPIdeal)

private noncomputable def foo' [DecidableEq B] [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    (DividedPowerAlgebra.dividedPowers' B ↥(J' I J)).DPMorphism (dividedPowers hI J)  := by

  /- convert DPMorphism.mk' _ _
    (Quotient.isDPMorphism (DividedPowerAlgebra.dividedPowers' B ↥(J' I J)) _) using 1 -/
  sorry

private noncomputable def β_aux [DecidableEq B] [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)]
    {α : (dividedPowers hI J).DPMorphism hK}
    (hα : α.comp (algebraMap B (dpEnvelope hI J)) = algebraMap B C) :
    (DividedPowerAlgebra.dividedPowers' B ↥(J' I J)).DPMorphism (h1 hK hI' hI'_int) where
  toRingHom  := ((α.toRingHom).comp (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))))
  ideal_comp := by
    rw [augIdeal_eq_generatedDpow_ι_range]
    simp only [SubDPIdeal.generatedDpow_carrier, map_span, span_le]
    rintro _ ⟨_, ⟨⟨n, hn, x, hx, rfl⟩, rfl⟩⟩
    simp only [SetLike.mem_coe, LinearMap.mem_range, Subtype.exists] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    simp only [J', Submodule.add_eq_sup, Submodule.mem_sup] at hb
    rw [DividedPowerAlgebra.dpow_ι]
    simp only [dpIdeal, SetLike.mem_coe, SubDPIdeal.memCarrier]
    simp only [K1, Submodule.add_eq_sup, RingHom.coe_comp, DPMorphism.coe_toRingHom,
      Function.comp_apply]
    obtain ⟨j, hj, i, hi, rfl⟩ := hb
    have : (⟨j + i, hb⟩ : ↥(J' I J)) = ⟨j, Ideal.mem_sup_left hj⟩ + ⟨i, Ideal.mem_sup_right hi⟩ :=
      rfl
    rw [this]
    rw [dp_add] -- TODO: general lemma?
    rw [← DPMorphism.toRingHom_apply]
    simp only [map_sum, _root_.map_mul, DPMorphism.toRingHom_apply]
    apply Ideal.sum_mem
    intros c hc
    by_cases hc1 : c.1 = 0
    · have hα1 : α 1 = 1 := sorry
      rw [hc1]
      simp only [dp_zero, map_one, hα1, one_mul]
      --rw [dp_def]
      apply Ideal.mem_sup_left
      have halg : algebraMap A C = (algebraMap B C).comp (algebraMap A B) :=
        IsScalarTower.algebraMap_eq A B C
      rw [halg, ← hα]
      rw [← Ideal.map_map, ← Ideal.map_map]
      rw [← α.toRingHom_apply]
      apply Ideal.mem_map_of_mem
      -- Idea: commute mk and dp + use dpow_ι

      /- convert Ideal.mem_map_of_mem ?_ hi
      have : (algebraMap B (DividedPowerAlgebra B ↥(J' I J) ⧸ J12 hI (J' I J) (sub_ideal_J' I J))) =
        (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))).comp
          (algebraMap B (DividedPowerAlgebra B ↥(J' I J))) := by
        simp only [Quotient.mk_comp_algebraMap]
      unfold dpEnvelope dpEnvelopeOfIncluded
      rw [this]
      rw [RingHom.comp_apply]
      congr 1 -/
      --apply Ideal.mem_map_of_mem
      sorry

    · apply Ideal.mem_sup_right
      apply Ideal.mul_mem_right
      apply α.ideal_comp
      rw [← α.toRingHom_apply]
      rw [dp_def]
      apply Ideal.mem_map_of_mem
      unfold dpIdeal
      sorry
  dpow_comp  := by
    intro n b hb'
    rw [h1_def]
    have := α.dpow_comp (n := n)
    sorry

set_option pp.proofs true
private noncomputable def β [DecidableEq B] [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)]
    {α : (dividedPowers hI J).DPMorphism hK}
    (hα : α.comp (algebraMap B (dpEnvelope hI J)) = algebraMap B C) :
    (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
      (J12_IsSubDPIdeal hI _ (sub_ideal_J' I J))).DPMorphism (h1 hK hI' hI'_int) where
  toRingHom  := α.toRingHom
  ideal_comp := by
    -- The map is a divided power morphism
    -- The target ideal is a divided power ideal
    -- To prove inclusion, it suffices to prove that generators for the source ideal (as a dp ideal)
    -- map to the target
    -- By lemma `augIdeal_eq_generatedDpow_ι_range` from `DPAlgebra/Dpow`,
    -- the elements of `J' I J` are such generators
    -- and it is basically obvious that they map to `K1`
    -- But, the elements of `J` map to `K` (hypothesis)
    -- and the elements of `I` map to `K` as well (another hypothesis)
    have hKK1 : K ≤ K1 I K := le_sup_right
    rw [Ideal.map_map, augIdeal_eq_generatedDpow_ι_range]
    set aux : (DividedPowerAlgebra.dividedPowers' B ↥(J' I J)).DPMorphism (h1 hK hI' hI'_int) :=
        β_aux hI J hK hI' /- hI'_ext -/ hI'_int hα
    have heq : aux =
        ((α.toRingHom).comp (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J)))) := rfl
    rw [← heq]
    exact map_generatedDpow_le aux (ι_range_subset_augIdeal B ↥(J' I J))
  dpow_comp  := fun {n} a ha => by
    have halg : algebraMap A C = (algebraMap B C).comp (algebraMap A B) :=
        IsScalarTower.algebraMap_eq A B C
    obtain ⟨hK', hmap, hint⟩ := isCompatibleWith_hI_h1 hI hK hI' hI'_int hI'_ext
    simp only [K1, Submodule.add_eq_sup, le_sup_left, inf_of_le_left] at hint
    simp only [halg, ← hα, ← map_map] at hint
    rw [augIdeal_eq_generatedDpow_ι_range] at ha
    simp only [SubDPIdeal.generatedDpow_carrier, SetLike.mem_coe, LinearMap.mem_range,
      Subtype.exists, exists_prop', nonempty_prop, ne_eq, Nat.exists_ne_zero, map_span] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · intros c hc
      simp only [Set.mem_image, Set.mem_setOf_eq] at hc
      obtain ⟨d, ⟨m, d', ⟨⟨b, hb, rfl⟩, rfl⟩⟩, rfl⟩ := hc
      rw [DividedPowerAlgebra.dpow_ι]
      simp only [Submodule.add_eq_sup, h1, DPMorphism.toRingHom_apply]
      simp only [J', Submodule.add_eq_sup] at hb
      rw [IdealAdd.dpow_eq_of_mem_right]
      have α_comp := α.dpow_comp (n := n)
      have hmap' : (algebraMap B (dpEnvelope hI J)) =
          (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))).comp
            (algebraMap B (DividedPowerAlgebra B ↥(J' I J))) := rfl
      · have hin : (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))) (dp B (m + 1) ⟨b, hb⟩)
            ∈ (dpIdeal hI J).carrier := by
          simp only [dpIdeal, SubDPIdeal.generatedDpow_carrier]

          sorry
        unfold dpEnvelope dpEnvelopeOfIncluded at α_comp
        rw [← DPMorphism.toRingHom_apply]
        rw [α_comp]
        simp only [dividedPowers]
        rw [IsSubDPIdeal.dpow_eq_of_mem]
        rfl
        · exact hin
        · exact hin
      ·
        have hmap' : (algebraMap B (dpEnvelope hI J)) =
          (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))).comp
            (algebraMap B (DividedPowerAlgebra B ↥(J' I J))) := rfl
        rw [hmap'] at hα
        sorry

    · sorry
    · sorry
    · sorry
    --have := α.ideal_comp
    /- have α_comp := α.dpow_comp
    rw [Ideal.map] at ha
    refine Submodule.span_induction' ?_ ?_ ?_ ?_ ha
    · intro c hc
      simp only [Set.mem_image, SetLike.mem_coe, RingHom.mem_ker] at hc
      obtain ⟨b, hb, rfl⟩ := hc
      have hb_in :  (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J))) b ∈
        (dpIdeal hI J).carrier := by
        simp only [dpIdeal, SubDPIdeal.memCarrier, SubDPIdeal.generatedDpow]
        apply subset_span
        simp only [SetLike.mem_coe, exists_prop', nonempty_prop, ne_eq, Nat.exists_ne_zero,
          Set.mem_setOf_eq]

        sorry
      sorry
    sorry
    · intros x hx y hy
      sorry
    sorry -/

    /- have ha' : a ∈ (dpIdeal hI J).carrier := sorry
    rw [h1]
    rw [IdealAdd.dpow_eq_of_mem_right]
    · unfold dpEnvelope dpEnvelopeOfIncluded at α_comp
      simp only [α_comp n a ha', dividedPowers, IsSubDPIdeal.dpow_eq_of_mem _ _ ha']
      rfl
    --rw [← hα] at hmapc
    --simp_rw [← hI'_ext] at hmap
    --rw φ.dpow_comp,
    · sorry -/

-- Universal property claim of Theorem 3.19
theorem dpEnvelope_IsDPEnvelope [DecidableEq B] [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    IsDPEnvelope hI J (dpIdeal hI J) (dividedPowers hI J)
      (algebraMap B (dpEnvelope hI J)) (sub_ideal_dpIdeal hI J) := by
  rintro C _ _ _ _ K hK hJK ⟨hI', hI'_ext, hI'_int⟩
  set φ := φ hI J hK hJK hI' hI'_ext hI'_int
  have hφ := hφ hI J hK hJK hI' hI'_ext hI'_int
  have hφ_unique := hφ_unique hI J hK hJK hI' hI'_ext hI'_int
  dsimp at hφ_unique
  use ψ hI J hK hJK hI' hI'_ext hI'_int
  refine ⟨by rw [← hφ]; rfl, fun α hα ↦ ?_⟩
  dsimp at hα
  ext x
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  set foo := β hI J hK hI' hI'_ext hI'_int hα
  rw [← hφ_unique (β hI J hK hI' hI'_ext hI'_int hα) hα, β]

end dpEnvelope_IsDPEnvelope
