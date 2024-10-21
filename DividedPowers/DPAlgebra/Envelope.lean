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
    (hI'_int : ∀ {n : ℕ}, ∀ b ∈ J ⊓ map (algebraMap A B) I, hJ.dpow n b = hI'.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers hJ hI' hI'_int).dpow n ((algebraMap A B) a) =
      (algebraMap A B) (hI.dpow n a) := by
  rw [← hI'_ext]
  exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int (mem_map_of_mem (algebraMap A B) ha)

end IdealAdd

namespace DividedPowers

/-- B-O Universal property from Theorem 3.19 -/
def IsDPEnvelope {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] [Algebra A B] (J : Ideal B) {D : Type v} [CommRing D] (J' : Ideal D)
    (hJ' : DividedPowers J') (ψ : B →+* D) (_ : J.map ψ ≤ J') :=
  ∀ (C : Type w) [CommRing C],
    ∀ [Algebra A C] [Algebra B C],
      ∀ [IsScalarTower A B C],
        ∀ (K : Ideal C) (hK : DividedPowers K)
          (_ : J.map (algebraMap B C) ≤ K)
          (_ : IsCompatibleWith hI hK (algebraMap A C)),
          ∃! φ : DPMorphism hJ' hK, φ.toRingHom ∘ ψ = algebraMap B C

/-- B-O Universal property from Theorem 3.19, with additional restriction at the end of case 1 -/
def IsWeakDPEnvelope {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] [Algebra A B] (J : Ideal B) {D : Type v} [CommRing D] (J' : Ideal D)
    (hJ' : DividedPowers J') (ψ : B →+* D) (_ : J.map ψ ≤ J') :=
  ∀ (C : Type w) [CommRing C],
    ∀ [Algebra A C] [Algebra B C],
      ∀ [IsScalarTower A B C],
        ∀ (K : Ideal C) (hK : DividedPowers K)
          (_ : J.map (algebraMap B C) ≤ K)
          (_ : I.map (algebraMap A C) ≤ K)
          (_ : IsCompatibleWith hI hK (algebraMap A C)),
          ∃! φ : DPMorphism hJ' hK, φ.toRingHom ∘ ψ = algebraMap B C

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

-- (DividedPowerAlgebra.ι B J x) is the map φ in B-O
-- (i)
inductive rel1 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : J} : rel1 (ι B J x) (algebraMap _ _ (x : B))

variable {J} in
lemma rel1_apply (x : J) :
  rel1 J ((ι B ↥J) x) ((algebraMap B (DividedPowerAlgebra B ↥J)) ↑x) := by constructor

-- J1
noncomputable def J1 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel1 J)

-- (ii)
/- inductive rel2 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2 (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (algebraMap _ _ (algebraMap A B (dpow hI n x))) -/

lemma algebraMap_dpow_mem (hIJ : I.map (algebraMap A B) ≤ J) (x : I) {n : ℕ} (hn : n ≠ 0) :
    algebraMap _ _ (algebraMap A B (dpow hI n x)) ∈ J := by
  apply hIJ
  simp only [Algebra.id.map_eq_id, RingHomCompTriple.comp_apply]
  exact Ideal.mem_map_of_mem _ (dpow_mem _ hn x.2)

-- (ii)'
inductive rel2' : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2' (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap _ _ (algebraMap A B (dpow hI n x))), algebraMap_dpow_mem hI J hIJ x hn⟩)

variable {J} in
lemma rel2'_apply {x : I} {n : ℕ} (hn : n ≠ 0) :
  rel2' hI J hIJ (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap _ _ (algebraMap A B (dpow hI n x))), algebraMap_dpow_mem hI J hIJ x hn⟩)
      := rel2'.Rel hn

-- J2
noncomputable def J2 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel2' hI J hIJ)

-- J in B-O
noncomputable def J12 : Ideal (DividedPowerAlgebra B J) :=
  J1 J + J2 hI J hIJ

variable {J}

lemma rel1_mem_J1 (x : J) :
    ((ι B ↥J) x - ((algebraMap B (DividedPowerAlgebra B ↥J)) ↑x)) ∈ J1 J := by
  rw [J1, ofRel]
  apply subset_span
  simp only [Set.mem_setOf_eq]
  use (ι B ↥J) x, (algebraMap B (DividedPowerAlgebra B ↥J)) ↑x
  constructor
  · exact rel1_apply x
  simp only [sub_add_cancel]

-- TODO: we might need something similar for rel2
lemma rel1_mem_J12 (x : J) :
    ((ι B ↥J) x - ((algebraMap B (DividedPowerAlgebra B ↥J)) ↑x)) ∈ J12 hI J hIJ :=
  mem_sup_left (rel1_mem_J1 x)

  /- inductive rel2' : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2' (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap _ _ (algebraMap A B (dpow hI n x))), algebraMap_dpow_mem hI J hIJ x hn⟩)-/

  lemma rel2_mem_J2 (x : I) {n : ℕ} (hn : n ≠ 0) :
    (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J)) -
    (ι B J ⟨(algebraMap _ _ (algebraMap A B (dpow hI n x))), algebraMap_dpow_mem hI J hIJ x hn⟩) ∈
    J2 hI J hIJ := by
  rw [J2, ofRel]
  apply subset_span
  simp only [Set.mem_setOf_eq]
  use ?_, ?_
  constructor
  · sorry--apply rel2'_apply
    --have := rel2'_apply hI hIJ hn (x := x)
  --rel2'_apply

  /- use (ι B ↥J) x, (algebraMap B (DividedPowerAlgebra B ↥J)) ↑x
  constructor
  · exact rel1_apply x
  simp only [sub_add_cancel] -/
  sorry
  sorry
  sorry


-- B-O : Claim in pg 61, proof in pg 62
theorem J12_IsSubDPIdeal [DecidableEq B] :
    IsSubDPIdeal (DividedPowerAlgebra.dividedPowers' B J)
      (J12 hI J hIJ ⊓ DividedPowerAlgebra.augIdeal B J) where
  isSubideal := inf_le_right
  dpow_mem   := fun hn x hx ↦ by
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
      exact hss (hsub.dpow_mem hn hx1)
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


variable (J)

-- 𝒟 at the end of pg 62 in B-O
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

-- J_bar in B-O
noncomputable def dpIdealOfIncluded [DecidableEq B] : Ideal (dpEnvelopeOfIncluded hI J hIJ) :=
  map (Ideal.Quotient.mk (J12 hI J hIJ)) (DividedPowerAlgebra.augIdeal B J)

-- J_bar has DP
theorem sub_ideal_dpIdealOfIncluded [Nontrivial B] [DecidableEq B] :
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
    have : algebraMap (DividedPowerAlgebra B ↥J) (dpEnvelopeOfIncluded hI J hIJ) =
      Ideal.Quotient.mk (J12 hI J hIJ) := rfl
    simp_rw [this]
    suffices y ∈ (augIdeal B J) ⊔ (J12 hI J hIJ) by
      rw [Submodule.mem_sup] at this
      obtain ⟨y, hy, z, hz, rfl⟩ := this
      use y, hy
      erw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      simp only [add_sub_cancel_left, hz]
    apply Submodule.span_induction hyJ (p := fun y ↦ y ∈ (augIdeal B J) ⊔ (J12 hI J hIJ))
    · intro x hx
      simp only [Set.mem_image, SetLike.mem_coe] at hx
      obtain ⟨y, hyJ, hyx⟩ := hx
      have hι : ((ι B ↥J) ⟨y, hyJ⟩) ∈ augIdeal B J := by
        rw [ι_def, dp_mem_augIdeal_iff]; exact zero_lt_one
      have hsub : (((algebraMap B (DividedPowerAlgebra B ↥J)) y) - (ι B ↥J) ⟨y, hyJ⟩) ∈
          J12 hI J hIJ := by
        rw [← neg_sub, Ideal.neg_mem_iff]
        exact rel1_mem_J12 _ _ _
      rw [Submodule.mem_sup]
      use ((ι B ↥J) ⟨y, hyJ⟩), hι,
        (((algebraMap B (DividedPowerAlgebra B ↥J)) y) - (ι B ↥J) ⟨y, hyJ⟩), hsub
      rw [← hyx]
      ring
    · exact Submodule.zero_mem _
    · intro x y hx hy
      simp only [Submodule.mem_sup] at hx hy ⊢
      obtain ⟨ax, hax, cx, hcx, hx⟩ := hx
      obtain ⟨ay, hay, cy, hcy, hy⟩ := hy
      use (ax + ay), Ideal.add_mem _ hax hay, (cx + cy), Ideal.add_mem _ hcx hcy
      simp only [← hx, ← hy]
      ring
    · intro a x hx
      simp only [Submodule.mem_sup] at hx ⊢
      obtain ⟨bx, hbx, cx, hcx, hx⟩ := hx
      use a • bx, Submodule.smul_mem _ a hbx, a • cx, Submodule.smul_mem _ a hcx
      rw [← hx, smul_add]
  exact Quotient.mk_surjective

-- Second part of Theorem 3.19
lemma isCompatibleWith_of_included [Nontrivial B] [DecidableEq B]
    [∀ x, Decidable (x ∈ (dpIdealOfIncluded hI J hIJ).carrier)] :
    IsCompatibleWith hI (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J)
      (J12_IsSubDPIdeal hI hIJ)) (algebraMap A (dpEnvelopeOfIncluded hI J hIJ)) := by
  set hJ := (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J)
      (J12_IsSubDPIdeal hI hIJ))
  --have hIJ : ∀ (n : ℕ), ∀ a ∈ I ⊓ J, hI.dpow n a = hJ.dpow n a := sorry
  --have := (IsCompatibleWith_tfae hI hJ (algebraMap A (dpEnvelopeOfIncluded hI J hIJ))).out 0 1
  --rw [← extends_to_def, extends_to_iff_exists_dpIdeal] at this
  rw [IsCompatibleWith]
  have I' := I.map (algebraMap A (dpEnvelopeOfIncluded hI J hIJ))
  have J' := (augIdeal B J).map (Ideal.Quotient.mk (J12 hI J hIJ))

  have : extends_to hI (algebraMap A (dpEnvelopeOfIncluded hI J hIJ)) := by
    rw [extends_to_iff_exists_dpIdeal]
    use dpIdealOfIncluded hI J hIJ
    use (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J) (J12_IsSubDPIdeal hI hIJ))
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
  refine Submodule.span_induction' ?_ ?_ ?_ ?_ hb'
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
    apply IdealAdd.dividedPowers hI' (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J)
      (J12_IsSubDPIdeal hI hIJ))

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
theorem dpEnvelopeOfIncluded_IsWeakDPEnvelope [Nontrivial B] [DecidableEq B] :
    IsWeakDPEnvelope hI J (dpIdealOfIncluded hI J hIJ)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J) (J12_IsSubDPIdeal hI hIJ))
      (algebraMap B (dpEnvelopeOfIncluded hI J hIJ)) (sub_ideal_dpIdealOfIncluded hI J hIJ) := by
  rw [IsWeakDPEnvelope]
  intro C _ _ _ _ K hK hJK hIK hcomp
  simp only [IsCompatibleWith, mem_inf, and_imp] at hcomp
  have hAC : hI.IsDPMorphism hK (algebraMap A C) := {
    left  := hIK
    right := by
      obtain ⟨hI', h, hh⟩ := hcomp
      --rw [isDPMorphism] at h
      intro n a haI
      rw [← hh ((algebraMap A C) a) (mem_map_of_mem (algebraMap A C) haI)]
      rw [h.2 a haI]
      exact (hIK (mem_map_of_mem (algebraMap A C) haI)) -- Q : Why does this appear??
  }
  have hDC : (DividedPowerAlgebra.dividedPowers' B J).IsDPMorphism hK (sorry) := sorry

  sorry

end Included

-- 2.4 in B. (with compatibility property)
section General

variable (I)

-- Ideal J1 in page 63 (general case)
def J' : Ideal B :=
  J + I.map (algebraMap A B)

-- IB is a subideal of J'
theorem sub_ideal_J' : I.map (algebraMap A B) ≤ J' I J :=
  le_sup_of_le_right (le_refl _)

variable {I}

 -- 𝒟_B,γ(J₁)
def dpEnvelope : Type v :=
  DividedPowerAlgebra B (J' I J) ⧸ J12 hI (J' I J) (sub_ideal_J' I J)

noncomputable instance : CommRing (dpEnvelope hI J) :=
  Ideal.Quotient.commRing _

noncomputable instance : Algebra B (dpEnvelope hI J) :=
  Ideal.Quotient.algebra _

noncomputable instance algebra' : Algebra A (dpEnvelope hI J) :=
  ((algebraMap B (dpEnvelope hI J)).comp (algebraMap A B)).toAlgebra

noncomputable instance algebra'' : Algebra (DividedPowerAlgebra B (J' I J)) (dpEnvelope hI J) :=
  Ideal.Quotient.algebra _

instance : IsScalarTower A B (dpEnvelope hI J) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

section DecidableEq

variable [DecidableEq B]

-- J₁_bar
noncomputable def J₁_bar : Ideal (dpEnvelope hI J) :=
  dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J)

-- The divided power structure on the DP envelope associated to `J₁_bar hI J`.
noncomputable def dividedPowers' : DividedPowers (J₁_bar hI J) :=
  Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
    (J12_IsSubDPIdeal hI (sub_ideal_J' I J))
/-
lemma J_le_augIdeal :
    J.map (algebraMap B (DividedPowerAlgebra B (J' I J))) ≤ (augIdeal B ↥(J' I J)) := sorry

noncomputable def dpIdeal' : (dividedPowers' B ↥(J' I J)).SubDPIdeal :=
  SubDPIdeal.generatedDpow (DividedPowerAlgebra.dividedPowers' B (J' I J)) (J_le_augIdeal J) -/

variable [Nontrivial B]

lemma J_le_J₁_bar : (map (algebraMap B (dpEnvelope hI J)) J) ≤ (J₁_bar hI J) := by
  have hss : map (algebraMap B (dpEnvelope hI J)) (J' I J) ≤ J₁_bar hI J := by
    rw [J₁_bar]
    apply sub_ideal_dpIdealOfIncluded
  exact le_trans (map_mono (le_sup_of_le_left (le_refl _))) hss

-- J_bar in pg 63 of B-O
noncomputable def dpIdeal : (dividedPowers' hI J).SubDPIdeal :=
  SubDPIdeal.generatedDpow (dividedPowers' hI J) (J_le_J₁_bar hI J)

-- First claim in Theorem 3.19 : `J⬝D_{B, γ} ⊆ J_bar`.
theorem sub_ideal_dpIdeal :
    J.map (algebraMap B (dpEnvelope hI J)) ≤ (dpIdeal hI J).carrier := by
  rw [dpIdeal, SubDPIdeal.generatedDpow_carrier]
  intros x hx
  apply subset_span
  use 1, one_ne_zero, x, hx, (dpow_one _ (J_le_J₁_bar _ _ hx)).symm

noncomputable def dividedPowers [∀ x, Decidable (x ∈  (dpIdeal hI J).carrier)] :
    DividedPowers (dpIdeal hI J).carrier :=
  IsSubDPIdeal.dividedPowers (dividedPowers' hI J) (dpIdeal hI J).toIsSubDPIdeal

-- I am not sure this is the right approach
-- Need compatibility btw I, ker f
-- x ∈ I ∩ ker f, dpow n x ∈ ker f (for n > 0)
noncomputable def dividedPowers_of_map {C : Type*} [CommRing C] (f : A →+* C)
    [∀ c, Decidable (c ∈ map f I)] : DividedPowers (I.map f) where
  dpow      := fun n c ↦
    if hc : c ∈ I.map f then by
      rw [Ideal.map, span, mem_span_set'] at hc
      set m := hc.choose with hm
      set fn := hc.choose_spec.choose with hfn
      set g := hc.choose_spec.choose_spec.choose with hg
      let hgc := hc.choose_spec.choose_spec.choose_spec
      rw [← hg, ← hfn] at hgc
      have hgi : ∀ i : Fin hc.choose, ∃ a : A, f a = g i := sorry
/-       let foo := (Finset.sym (Set.univ : Set (Fin hc.choose)) n).sum fun k =>
        (Set.univ : Set (Fin hc.choose)).prod fun i => hI.dpow (Multiset.count i k) (hgi i).choose-/
      sorry
    else 0
  dpow_null hc := by simp only [dif_neg hc]
  dpow_zero := by
    intro c hc
    simp only [dif_pos hc]
    --simp_rw [dpow_zero]
    sorry
  dpow_one  := sorry
  dpow_mem  := sorry
  dpow_add  := sorry
  dpow_smul := sorry
  dpow_mul  := sorry
  dpow_comp := sorry

-- Second part of Theorem 3.19
lemma isCompatibleWith [∀ x, Decidable (x ∈ (dpIdeal hI J).carrier)] :
    IsCompatibleWith hI (dividedPowers hI J) (algebraMap A (dpEnvelope hI J)) := by
  rw [IsCompatibleWith]
  sorry

end DecidableEq
section

variable [Nontrivial B]

-- Universal property claim of Theorem 3.19
theorem dpEnvelope_IsDPEnvelope [DecidableEq B] [∀ x, Decidable (x ∈  (dpIdeal hI J).carrier)] :
    IsDPEnvelope hI J (dpIdeal hI J)
      (dividedPowers hI J)
      (algebraMap B (dpEnvelope hI J)) (sub_ideal_dpIdeal hI J) := by
  rw [IsDPEnvelope]
  rintro C _ _ _ _ K hK hJK ⟨hI', hI'_ext, hI'_int⟩
  -- K1 in page 63 of B-O
  set K1 : Ideal C := I.map (algebraMap A C) + K with hK1
  -- δ' in page 63 of B-O
  set h1 : DividedPowers K1 := IdealAdd.dividedPowers hI' hK hI'_int with h1_def
  set g' : hI.DPMorphism h1 :=
    { toRingHom  := algebraMap A C
      ideal_comp := le_sup_of_le_left (le_refl _)
      dpow_comp  := fun a ha => by sorry
      /- IdealAdd.dividedPowers_dpow_eq_algebraMap hI hK hI' hI'_ext hI'_int _ _ ha -/}
  have hg' : (J' I J).map (algebraMap B C) ≤ K1 := by
    rw [J', Ideal.add_eq_sup, Ideal.map_sup, sup_le_iff]
    refine ⟨le_trans hJK (le_sup_of_le_right (le_refl _)), ?_⟩
    · rw [Ideal.map_map, Eq.symm (IsScalarTower.algebraMap_eq A B C)]
      exact le_sup_of_le_left (le_refl _)
  have hI1 : IsCompatibleWith hI h1 (algebraMap A C) := by
    rw [IsCompatibleWith]
    use hI'; use hI'_ext
    intro n c hc
    simp only [hK1, Ideal.add_eq_sup, inf_of_le_right, le_sup_right] at hc
    rw [eq_comm]
    exact IdealAdd.dpow_eq_of_mem_left _ _ hI'_int hc.1
  obtain ⟨φ, hφ, hφ_unique⟩ := by
    refine dpEnvelopeOfIncluded_IsWeakDPEnvelope hI (J' I J) (sub_ideal_J' I J) C _ h1 hg' ?_ hI1
    sorry

  -- TODO: generalize (map to sub-pd-structure)
  set ψ : (dividedPowers hI J).DPMorphism hK :=
    { toRingHom  := φ.toRingHom
      ideal_comp := by
        have := φ.ideal_comp
        have hKK1 : K ≤ K1 := sorry
        intros x hx
        --simp? at hx

        have hx' : x ∈ map φ.toRingHom (dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J)) := sorry
        specialize this
        sorry

      dpow_comp  := fun a ha => by
        --have := φ.dpow_comp
        obtain ⟨r, s⟩ := hI1
        --rw ← hI'_ext,
        --rw φ.dpow_comp,
        sorry }
  use ψ
  --simp only,
  use hφ
  intro α hα

  set β : (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
    (J12_IsSubDPIdeal hI (sub_ideal_J' I J))).DPMorphism h1 :=
  { toRingHom  := α.toRingHom
    ideal_comp := by
      have hKK1 : K ≤ K1 := sorry
      apply le_trans _ hKK1
      have := α.ideal_comp
      apply le_trans _ this
      apply Ideal.map_mono
      rw [Ideal.map_le_iff_le_comap]
      intros x hx
      rw [Ideal.mem_comap]
      simp only [augIdeal] at hx
      /- simp only [dpIdeal]
      convert sub_ideal_dpIdeal hI J
      simp only [dpEnvelope] -/

      sorry
    dpow_comp  := fun a ha => by
      obtain ⟨hK', hmap, hint⟩ := hI1
      --rw [← hα] at hmap
      --simp_rw [← hI'_ext] at hmap
      --rw φ.dpow_comp,
      sorry }

  have hβ : β.toRingHom ∘ ⇑(algebraMap B (dpEnvelopeOfIncluded hI (J' I J)
    (sub_ideal_J' I J))) = ⇑(algebraMap B C) := sorry

  ext x
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [← hφ_unique β hβ]
