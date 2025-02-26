/-
Copyright (c) 2022 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.DPMorphism
import Mathlib.RingTheory.Ideal.Quotient.Operations

open Subtype

-- TODO: move
theorem Ideal.iSup_eq_span {A : Type*} [CommSemiring A] {ι : Type*} (p : ι → Ideal A) :
    (⨆ i, p i) = Ideal.span (⋃ i, ↑(p i)) :=
  Submodule.iSup_eq_span p

-- We should PR this lemma
theorem Submodule.iSup_eq_span' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {ι : Sort _} (p : ι → Submodule R M) (h : ι → Prop) :
    (⨆ (i : ι) (_ : h i), p i) = Submodule.span R (⋃ (i : ι) (_ : h i), ↑(p i)) := by
  simp_rw [← Submodule.iSup_span, Submodule.span_eq]

-- Is any of this is in Mathlib? For Submodule, maybe?
namespace Subideal

variable {A : Type*} [CommSemiring A] {I : Ideal A}

/-- The Galois coinsertion between the map sending a subideal `J ≤ I` to itself,
  and the mal sending `J ↦ J ⊓ I`. -/
def galoisCoinsertion :
    GaloisCoinsertion (fun J : { J : Ideal A // J ≤ I } ↦ (J : Ideal A))
      (fun J : Ideal A ↦ ⟨J ⊓ I, inf_le_right⟩) :=
  GaloisCoinsertion.monotoneIntro (fun _ _ h ↦ mk_le_mk.mpr (inf_le_inf_right I h))
    (fun _ _ h ↦ h) (fun _ ↦ inf_le_left)
    (fun ⟨J, hJ⟩ ↦ by simp only [ge_iff_le, mk.injEq, inf_eq_left, hJ])

instance : CompleteLattice { J : Ideal A // J ≤ I } :=
  GaloisCoinsertion.liftCompleteLattice galoisCoinsertion

theorem top_def : (⟨I, le_refl I⟩ : { J : Ideal A // J ≤ I }) = ⊤ :=
  eq_top_iff.mpr (⊤ : { J : Ideal A // J ≤ I }).property

theorem bot_def : (⟨⊥, bot_le⟩ : { J : Ideal A // J ≤ I }) = ⊥ := by rw [mk_bot]

theorem inf_def (J J' : { J : Ideal A // J ≤ I }) :
  (J ⊓ J' : { J : Ideal A // J ≤ I }) =
    ⟨(J : Ideal A) ⊓ (J' : Ideal A), inf_le_of_left_le J.2⟩ := by
  ext x
  exact ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, J.property h.left⟩⟩

theorem sInf_def (S : Set { J : Ideal A // J ≤ I }) :
    (sInf S : { J : Ideal A // J ≤ I }) = ⟨sInf (val '' S) ⊓ I, inf_le_right⟩ := rfl

theorem sup_def (J J' : { J : Ideal A // J ≤ I }) :
    (J ⊔ J' : { J : Ideal A // J ≤ I }) = ⟨sInf {B | (J : Ideal A) ≤ B ∧ (J' : Ideal A) ≤ B},
      sInf_le_of_le ⟨J.2, J'.2⟩ (le_refl I)⟩ := by
  ext x
  exact ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, Submodule.mem_sInf.mp h I ⟨J.2, J'.2⟩⟩⟩

theorem sSup_def (S : Set { J : Ideal A // J ≤ I }) :
    (sSup S : { J : Ideal A // J ≤ I }) = ⟨sSup (val '' S) ⊓ I, inf_le_right⟩ := rfl

end Subideal

namespace DividedPowers

/-- The structure of a sub-dp-ideal of a dp-ideal -/
structure IsSubDPIdeal {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)
    (J : Ideal A) : Prop where
  isSubideal : J ≤ I
  dpow_mem : ∀ (n : ℕ) (_: n ≠ 0) {j : A} (_ : j ∈ J), hI.dpow n j ∈ J
section  IsSubDPIdeal

namespace IsSubDPIdeal

variable {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)

open Ideal

theorem self : IsSubDPIdeal hI I where
  isSubideal := le_rfl
  dpow_mem _ hn _ ha := hI.dpow_mem hn ha

/-- The divided power structure on a sub-dp-ideal. -/
def dividedPowers {J : Ideal A} (hJ : IsSubDPIdeal hI J) [∀ x, Decidable (x ∈ J)] :
    DividedPowers J where
  dpow n x        := if x ∈ J then hI.dpow n x else 0
  dpow_null hx    := by simp only [if_neg hx]
  dpow_zero hx    := by simp only [if_pos hx, hI.dpow_zero (hJ.isSubideal hx)]
  dpow_one hx     := by simp only [if_pos hx, hI.dpow_one (hJ.isSubideal hx)]
  dpow_mem hn hx  := by simp only [if_pos hx, hJ.dpow_mem _ hn hx]
  dpow_add hx hy  := by simp_rw [if_pos hx, if_pos hy, if_pos (Ideal.add_mem J hx hy),
    hI.dpow_add (hJ.isSubideal hx) (hJ.isSubideal hy)]
  dpow_mul hx     := by
    simp only [if_pos hx, if_pos (mul_mem_left J _ hx), hI.dpow_mul (hJ.isSubideal hx)]
  mul_dpow hx     := by simp only [if_pos hx, hI.mul_dpow (hJ.isSubideal hx)]
  dpow_comp hn hx := by
    simp only [if_pos hx, if_pos (hJ.dpow_mem _ hn hx), hI.dpow_comp hn (hJ.isSubideal hx)]

variable {J : Ideal A} (hJ : IsSubDPIdeal hI J) [∀ x, Decidable (x ∈ J)]

lemma dpow_eq {n : ℕ} {a : A} :
    (IsSubDPIdeal.dividedPowers hI hJ).dpow n a = if a ∈ J then hI.dpow n a else 0 := rfl

lemma dpow_eq_of_mem {n : ℕ} {a : A} (ha : a ∈ J) :
    (IsSubDPIdeal.dividedPowers hI hJ).dpow n a = hI.dpow n a := by rw [dpow_eq, if_pos ha]

theorem isDPMorphism (hJ : IsSubDPIdeal hI J) :
    (IsSubDPIdeal.dividedPowers hI hJ).IsDPMorphism hI (RingHom.id A) := by
  simp only [isDPMorphism_iff, Ideal.map_id, RingHom.id_apply]
  exact ⟨hJ.1, fun _ _ _ ha ↦ by rw [dpow_eq_of_mem _ _ ha]⟩


end IsSubDPIdeal

open Finset Ideal

/-- The ideal `J ⊓ I` is a sub-dp-ideal of `I` if and only if (on `I`) the divided powers have
  some compatiblity mod `J`. (The necessity was proved as a sanity check.) -/
theorem IsSubDPIdeal_inf_iff {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {J : Ideal A} : IsSubDPIdeal hI (J ⊓ I) ↔
    ∀ {n : ℕ} {a b : A} (_ : a ∈ I) (_ : b ∈ I) (_ : a - b ∈ J), hI.dpow n a - hI.dpow n b ∈ J := by
  refine ⟨fun hIJ n a b ha hb hab ↦ ?_, fun hIJ ↦ ?_⟩
  · have hab' : a - b ∈ I := I.sub_mem ha hb
    rw [← add_sub_cancel b a, hI.dpow_add' hb hab', range_succ, sum_insert not_mem_range_self,
      tsub_self, hI.dpow_zero hab', mul_one,add_sub_cancel_left]
    exact J.sum_mem (fun i hi ↦  SemilatticeInf.inf_le_left J I ((J ⊓ I).smul_mem _
      (hIJ.dpow_mem _ (ne_of_gt (Nat.sub_pos_of_lt (mem_range.mp hi))) ⟨hab, hab'⟩)))
  · refine ⟨SemilatticeInf.inf_le_right J I, fun {n} hn {a} ha ↦ ⟨?_, hI.dpow_mem hn ha.right⟩⟩
    rw [← sub_zero (hI.dpow n a), ← hI.dpow_eval_zero hn]
    exact hIJ ha.right I.zero_mem (J.sub_mem ha.left J.zero_mem)

variable {A B : Type*} [CommSemiring A] {I : Ideal A} {hI : DividedPowers I} [CommSemiring B]
  {J : Ideal B} {hJ : DividedPowers J}

/-- Lemma 3.6 of [BO] (Antoine) -/
theorem span_IsSubDPIdeal_iff {S : Set A} (hS : S ⊆ I) :
    IsSubDPIdeal hI (span S) ↔ ∀ {n : ℕ} (_ : n ≠ 0), ∀ s ∈ S, hI.dpow n s ∈ span S := by
  refine ⟨fun hhI n hn s hs ↦ hhI.dpow_mem n hn (subset_span hs), ?_⟩
  · -- interesting direction,
    intro hhI
    have hSI := span_le.mpr hS
    apply IsSubDPIdeal.mk hSI
    intro m hm z hz
    -- This solution is a bit hacky, but it works...
    have haux : ∀ (n : ℕ), n ≠ 0 → hI.dpow n z ∈ span S := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      ·-- case of elements of S
        exact fun s hs n hn ↦ hhI hn s hs
      ·-- case of 0
        intro _ hn
        rw [hI.dpow_eval_zero hn]
        exact (span S).zero_mem
      · -- case of sum
        intro x y hxI hyI hx hy n hn
        rw [hI.dpow_add' (hSI hxI) (hSI hyI)]
        apply Submodule.sum_mem (span S)
        intro m _
        by_cases hm0 : m = 0
        · exact hm0 ▸ mul_mem_left (span S)  _ (hy _ hn)
        · exact mul_mem_right _ (span S) (hx _ hm0)
      · -- case : product,
        intro a x hxI hx n hn
        rw [Algebra.id.smul_eq_mul, hI.dpow_mul (hSI hxI)]
        exact mul_mem_left (span S) (a ^ n) (hx n hn)
    exact @haux m hm

theorem generated_dpow_isSubideal {S : Set A} (hS : S ⊆ I) :
    span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} ≤ I := by
  rw [span_le]
  rintro y ⟨n, hn, x, hx, hxy⟩
  exact hxy ▸ hI.dpow_mem hn (hS hx)

theorem IsSubDPIdeal_sup {J K : Ideal A} (hJ : IsSubDPIdeal hI J) (hK : IsSubDPIdeal hI K) :
    IsSubDPIdeal hI (J ⊔ K) := by
  rw [← J.span_eq, ← K.span_eq, ← span_union,
    span_IsSubDPIdeal_iff (Set.union_subset_iff.mpr ⟨hJ.1, hK.1⟩)]
  · intro n hn a ha
    rcases ha with ha | ha
    . exact span_mono Set.subset_union_left (subset_span (hJ.2 n hn ha))
    . exact span_mono Set.subset_union_right (subset_span (hK.2 n hn ha))

theorem IsSubDPIdeal_iSup {ι : Type*} {J : ι → Ideal A} (hJ : ∀ i, IsSubDPIdeal hI (J i)) :
    IsSubDPIdeal hI (iSup J) := by
  rw [iSup_eq_span, span_IsSubDPIdeal_iff (Set.iUnion_subset_iff.mpr <| fun i ↦ (hJ i).1)]
  simp_rw [Set.mem_iUnion]
  rintro n hn a ⟨i, ha⟩
  exact span_mono (Set.subset_iUnion _ i) (subset_span ((hJ i).2 n hn ha))

theorem IsSubDPIdeal_map_of_IsSubDPIdeal {f : A →+* B} (hf : IsDPMorphism hI hJ f) {K : Ideal A}
    (hK : IsSubDPIdeal hI K) : IsSubDPIdeal hJ (map f K) := by
  rw [Ideal.map, span_IsSubDPIdeal_iff]
  · rintro n hn y ⟨x, hx, rfl⟩
    exact hf.2 x (hK.1 hx) ▸ mem_map_of_mem _ (hK.2 _ hn hx)
  · rintro y ⟨x, hx, rfl⟩
    exact hf.1 (mem_map_of_mem f (hK.1 hx))

theorem IsSubDPIdeal_map {f : A →+* B} (hf : IsDPMorphism hI hJ f) :
    IsSubDPIdeal hJ (Ideal.map f I) :=
  IsSubDPIdeal_map_of_IsSubDPIdeal hf (IsSubDPIdeal.self hI)

end IsSubDPIdeal

/-- A `SubDPIdeal` of `I` is a sub-ideal `J` of `I` such that for all `n ∈ ℕ ≥ 0` and all
  `j ∈ J`, `hI.dpow n j ∈ J`. -/
@[ext]
structure SubDPIdeal {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I) where
  /-- The underlying ideal. -/
  carrier : Ideal A
  isSubideal : carrier ≤ I
  dpow_mem : ∀ (n : ℕ) (_ : n ≠ 0), ∀ j ∈ carrier, hI.dpow n j ∈ carrier

namespace SubDPIdeal

variable {A : Type*} [CommSemiring A] {I : Ideal A} {hI : DividedPowers I}

/-- Constructs a `SubPDIdeal` given an ideal `J` satisfying `hI.IsSubDPIdeal J`. -/
def mk' {J : Ideal A} (hJ : hI.IsSubDPIdeal J) : hI.SubDPIdeal := ⟨J, hJ.1, hJ.2⟩

instance : SetLike (SubDPIdeal hI) A where
  coe s := s.carrier
  coe_injective' p q h := by
    rw [SetLike.coe_set_eq] at h
    cases p ; cases q ; congr

/-- The coercion from `SubDPIdeal` to `Ideal`. -/
@[coe]
def toIdeal (J : hI.SubDPIdeal) : Ideal A := J.carrier

instance : CoeOut (hI.SubDPIdeal) (Ideal A) := ⟨fun J ↦ J.toIdeal⟩

theorem coe_def (J : SubDPIdeal hI) : J.toIdeal = J.carrier := rfl

@[simp]
theorem memCarrier {s : SubDPIdeal hI} {x : A} : x ∈ s.carrier ↔ x ∈ s := Iff.rfl

lemma toIsSubDPIdeal (J : SubDPIdeal hI) : IsSubDPIdeal hI J.carrier where
  isSubideal := J.isSubideal
  dpow_mem   := J.dpow_mem

open Ideal

lemma IsSubDPIdeal_of_SubDPIdeal (J : SubDPIdeal hI) :
    SubDPIdeal.mk' J.toIsSubDPIdeal = J := rfl

lemma SubDPIdeal_of_IsSubDPIdeal {J  : Ideal A} (hJ : IsSubDPIdeal hI J) :
    (SubDPIdeal.mk' hJ).toIsSubDPIdeal = hJ := rfl

/-- If J is an ideal of A, then I ⬝ J is a sub-dp-ideal of I. (Berthelot, 1.6.1 (i)) -/
def prod (J : Ideal A) : SubDPIdeal hI where
  carrier := I • J
  isSubideal := mul_le_right
  dpow_mem _ hm x hx := by
    have haux : ∀ (n : ℕ) (_ : n ≠ 0), hI.dpow n x ∈ I • J := by
      apply Submodule.smul_induction_on'
        (p := fun (x : A) (hxI : x ∈ I • J) ↦ ∀ (n : ℕ) (_ : n ≠ 0), hI.dpow n x ∈ I • J) hx
      · -- smul
        intro a ha b hb n hn
        rw [Algebra.id.smul_eq_mul, smul_eq_mul, mul_comm a b, hI.dpow_mul ha, mul_comm]
        exact Submodule.mul_mem_mul (J.pow_mem_of_mem hb n (zero_lt_iff.mpr hn))
          (hI.dpow_mem hn ha)
      · -- add
        intro x hx y hy hx' hy' n hn
        rw [hI.dpow_add' (mul_le_right hx) (mul_le_right hy)]
        apply Submodule.sum_mem (I • J)
        intro k _
        by_cases hk0 : k = 0
        · exact hk0 ▸ mul_mem_left (I • J) _ (hy' _ hn)
        · exact mul_mem_right _ (I • J) (hx' k hk0)
    exact @haux _ hm

section CompleteLattice

instance : CoeOut (SubDPIdeal hI) { J : Ideal A // J ≤ I } := ⟨fun J ↦ ⟨J.carrier, J.isSubideal⟩⟩

instance : LE (SubDPIdeal hI) := ⟨fun J J' ↦ J.carrier ≤ J'.carrier⟩

theorem le_iff {J J' : SubDPIdeal hI} : J ≤ J' ↔ J.carrier ≤ J'.carrier := Iff.rfl

instance : LT (SubDPIdeal hI) := ⟨fun J J' ↦ J.carrier < J'.carrier⟩

theorem lt_iff {J J' : SubDPIdeal hI} : J < J' ↔ J.carrier < J'.carrier := Iff.rfl

/-- I is a sub-dp-ideal ot itself. -/
instance : Top (SubDPIdeal hI) :=
  ⟨{carrier    := I
    isSubideal := le_refl _
    dpow_mem   := fun _ hn _ hx ↦ hI.dpow_mem hn hx }⟩

instance inhabited : Inhabited hI.SubDPIdeal := ⟨⊤⟩

/-- `(0)` is a sub-dp-ideal ot the dp-ideal `I`. -/
instance : Bot (SubDPIdeal hI) :=
  ⟨{carrier    := ⊥
    isSubideal := bot_le
    dpow_mem   := fun _ hn x hx ↦ by rw [mem_bot.mp hx, hI.dpow_eval_zero hn, mem_bot]}⟩

--Section 1.8 of [B]
-- The intersection of two sub-dp-ideals is a sub-dp-ideal.
instance : Min (SubDPIdeal hI) :=
  ⟨fun J J' ↦
    { carrier    := J.carrier ⊓ J'.carrier
      isSubideal := fun _ hx ↦ J.isSubideal hx.1
      dpow_mem   := fun _ hn x hx ↦ ⟨J.dpow_mem _ hn x hx.1, J'.dpow_mem _ hn x hx.2⟩ }⟩

theorem inf_carrier_def (J J' : SubDPIdeal hI) : (J ⊓ J').carrier = J.carrier ⊓ J'.carrier := rfl

instance : InfSet (SubDPIdeal hI) :=
  ⟨fun S ↦
    { carrier    := ⨅ s ∈ Insert.insert ⊤ S, (s : hI.SubDPIdeal).carrier
      isSubideal := fun x hx ↦ by
        simp only [mem_iInf] at hx
        exact hx ⊤ (Set.mem_insert ⊤ S)
      dpow_mem   := fun _ hn x hx ↦ by
        simp only [mem_iInf] at hx ⊢
        exact fun s hs ↦ s.dpow_mem _ hn x (hx s hs) }⟩

theorem sInf_carrier_def (S : Set (SubDPIdeal hI)) :
    (sInf S).carrier = ⨅ s ∈ Insert.insert ⊤ S, (s : hI.SubDPIdeal).carrier := rfl

instance : Max (SubDPIdeal hI) :=
  ⟨fun J J' ↦ SubDPIdeal.mk' (IsSubDPIdeal_sup J.toIsSubDPIdeal J'.toIsSubDPIdeal)⟩

theorem sup_carrier_def (J J' : SubDPIdeal hI) : (J ⊔ J').carrier = J ⊔ J' := rfl

instance : SupSet (SubDPIdeal hI) :=
  ⟨fun S ↦ SubDPIdeal.mk' (J := sSup ((fun J ↦ J.carrier) '' S)) <| by
      have h : (⋃ (i : Ideal A) (_ : i ∈ (fun J ↦ J.carrier) '' S), ↑i) ⊆ (I : Set A) := by
        rintro a ⟨-, ⟨J, rfl⟩, haJ⟩
        rw [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at haJ
        obtain ⟨J', hJ'⟩ := (Set.mem_image _ _ _).mp haJ.1
        exact  J'.isSubideal  (hJ'.2 ▸ haJ.2)
      rw [sSup_eq_iSup, Submodule.iSup_eq_span', submodule_span_eq, span_IsSubDPIdeal_iff h]
      rintro n hn x ⟨T, ⟨J, rfl⟩, ⟨J', ⟨⟨hJ', rfl⟩, h'⟩⟩⟩
      apply subset_span
      apply Set.mem_biUnion hJ'
      obtain ⟨K, hKS, rfl⟩ := hJ'
      exact K.dpow_mem _ hn x h'⟩

theorem sSup_carrier_def (S : Set (SubDPIdeal hI)) : (sSup S).carrier = sSup ((toIdeal) '' S) := rfl

instance : CompleteLattice (SubDPIdeal hI) := by
  refine Function.Injective.completeLattice (fun J : SubDPIdeal hI ↦ (J : { J : Ideal A // J ≤ I }))
    (fun J J' h ↦ by simpa only [SubDPIdeal.ext_iff, Subtype.mk.injEq] using h)
    (fun J J' ↦ by rw [Subideal.sup_def] ; rfl) (fun J J' ↦ by rw [Subideal.inf_def] ; rfl)
    (fun S ↦ ?_) (fun S ↦ ?_) (by rw [← Subideal.top_def] ; rfl ) (by rw [← Subideal.bot_def] ; rfl)
  · conv_rhs => rw [iSup]
    rw [Subideal.sSup_def, Subtype.ext_iff]
    dsimp only
    rw [sSup_carrier_def, sSup_image, sSup_image, iSup_range]
    have : ∀ J : hI.SubDPIdeal,
      ((⨆ (_ : J ∈ S), (J : { B : Ideal A // B ≤ I }) : { B : Ideal A // B ≤ I }) : Ideal A) =
        ⨆ (_ : J ∈ S), (J : Ideal A) := by
      intro J
      by_cases hJ : J ∈ S
      · simp only [ciSup_pos hJ]
      · simp only [hJ, iSup_false, coe_eq_bot_iff, bot_le]
    simp_rw [this]
    ext a
    refine' ⟨fun ha ↦ ⟨ha, _⟩, fun ha ↦ ha.1⟩
    apply (Submodule.mem_iSup _).mp ha I
    intro J
    by_cases hJ : J ∈ S
    · rw [ciSup_pos hJ];
      exact J.isSubideal
    · simp only [hJ, iSup_false, bot_le]
  · conv_rhs => rw [iInf]
    rw [Subideal.sInf_def, Subtype.ext_iff]
    dsimp only
    rw [sInf_carrier_def, sInf_image, iInf_range, iInf_inf, iInf_insert, inf_iInf]
    apply iInf_congr
    intro J
    by_cases hJ : J ∈ S
    · rw [ciInf_pos hJ, ciInf_pos hJ, inf_comm]; rfl
    · simp only [hJ, iInf_false, inf_top_eq, ← Subideal.top_def, coe_mk, inf_idem]; rfl

end CompleteLattice

section Generated

variable (hI)

/-- The sub-dp-ideal of I generated by a family of elements of A. -/
def generated (S : Set A) : SubDPIdeal hI := sInf {J : SubDPIdeal hI | S ⊆ J.carrier}

/-- The sub-dp-ideal of I generated by the family `hI.dpow n x`,
  where `n ≠ 0` and `x ∈ S`. -/
def generatedDpow {S : Set A} (hS : S ⊆ I) : SubDPIdeal hI where
  carrier := span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x}
  isSubideal := hI.generated_dpow_isSubideal hS
  dpow_mem _ hk z hz := by
    have hSI := hI.generated_dpow_isSubideal hS
    have haux : ∀ (n : ℕ) (_ : n ≠ 0),
        hI.dpow n z ∈ span {y | ∃ n, ∃ (_ : n ≠ 0), ∃ x, ∃ (_ : x ∈ S), y = hI.dpow n x} := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      · -- Elements of S
        rintro y ⟨m, hm, x, hxS, hxy⟩ n hn
        rw [hxy, hI.dpow_comp hm (hS hxS)]
        exact mul_mem_left _ _ (subset_span ⟨n * m, mul_ne_zero hn hm, x, hxS, rfl⟩)
      · -- Zero
        exact fun _ hn ↦ by simp only [hI.dpow_eval_zero hn, zero_mem]
      · intro x y hx hy hx_pow hy_pow n hn
        rw [hI.dpow_add' (hSI hx) (hSI hy)]
        apply Submodule.sum_mem (span _)
        intro m _
        by_cases hm0 : m = 0
        · rw [hm0]; exact (span _).mul_mem_left _ (hy_pow n hn)
        · exact (span _).mul_mem_right _ (hx_pow m hm0)
      · intro a x hx hx_pow n hn
        rw [smul_eq_mul, hI.dpow_mul (hSI hx)]
        exact mul_mem_left (span _) (a ^ n) (hx_pow n hn)
    exact haux _ hk

theorem generatedDpow_carrier {S : Set A} (hS : S ⊆ I) :
    (generatedDpow hI hS).carrier =
      span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} := rfl

theorem le_generatedDpow {S : Set A} (hS : S ⊆ I) : S ⊆ (generatedDpow hI hS).carrier := fun x hx ↦
  subset_span ⟨1, one_ne_zero, x, hx, by rw [hI.dpow_one (hS hx)]⟩

theorem generated_dpow_le (S : Set A) (J : SubDPIdeal hI) (hSJ : S ⊆ J.carrier) :
    span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} ≤ J.carrier := by
  rw [span_le]
  rintro y ⟨n, hn, x, hx, hxy⟩
  exact hxy ▸ J.dpow_mem n hn x (hSJ hx)

theorem generated_carrier_eq {S : Set A} (hS : S ⊆ I) :
    (generated hI S).carrier =
      span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} := by
  simp only [generated, sInf_carrier_def]
  apply le_antisymm
  · have h : generatedDpow hI hS ∈ insert ⊤ {J : hI.SubDPIdeal | S ⊆ ↑J.carrier} :=
      Set.mem_insert_of_mem _ (le_generatedDpow hI hS)
    refine sInf_le_of_le ⟨generatedDpow hI hS, ?_⟩ (le_refl _)
    simp only [h, ciInf_pos]
    rfl
  · rw [le_iInf₂_iff]
    intro J hJ
    apply generated_dpow_le hI S J
    rcases hJ with hJI | hJS
    exacts [hJI ▸ hS, hJS]

end Generated

end SubDPIdeal

section Ker

-- TODO : CommSemiring ?

variable {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {B : Type*} [CommRing B] {J : Ideal B} (hJ : DividedPowers J)

theorem IsSubDPIdeal_ker {f : A →+* B} (hf : IsDPMorphism hI hJ f) :
    IsSubDPIdeal hI (RingHom.ker f ⊓ I) := by
  rw [IsSubDPIdeal_inf_iff]
  simp only [IsDPMorphism] at hf
  intro n a b ha hb
  simp only [RingHom.sub_mem_ker_iff, ← hf.2 a ha, ← hf.2 b hb]
  exact congr_arg _

open Ideal

/-- The kernel of a divided power morphism, as a `SubDPIdeal`. -/
def DPMorphism.ker (f : DPMorphism hI hJ) : SubDPIdeal hI where
  carrier := RingHom.ker f.toRingHom ⊓ I
  isSubideal := inf_le_right
  dpow_mem _ hn a := by
    simp only [mem_inf, and_imp, RingHom.mem_ker]
    intro ha ha'
    rw [← f.isDPMorphism.2 a ha', ha]
    exact ⟨dpow_eval_zero hJ hn, hI.dpow_mem hn ha'⟩

end Ker

section Equalizer

variable {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)

/- TODO : The set of elements where two divided
powers coincide is the largest ideal which is a sub-dp-ideal in both -/

/-- The ideal of `A` in which the two divided power structures `hI` and `hI'` coincide. -/
def dpEqualizer {A : Type*} [CommSemiring A] {I : Ideal A} (hI hI' : DividedPowers I) : Ideal A
    where
  carrier := {a ∈ I | ∀ n : ℕ, hI.dpow n a = hI'.dpow n a}
  add_mem' {a b} ha hb := by
    apply And.intro (I.add_mem ha.1 hb.1) (fun n ↦ ?_)
    rw [hI.dpow_add ha.1 hb.1, hI'.dpow_add ha.1 hb.1]
    exact Finset.sum_congr rfl (fun k _ ↦ by rw [ha.2, hb.2])
  zero_mem' := by
    apply And.intro I.zero_mem (fun n ↦ ?_)
    by_cases hn : n = 0
    · rw [hn, hI.dpow_zero (zero_mem I), hI'.dpow_zero (zero_mem I)]
    · rw [hI.dpow_eval_zero hn, hI'.dpow_eval_zero hn]
  smul_mem' a x hx := by
    rw [Algebra.id.smul_eq_mul]
    exact ⟨I.mul_mem_left a hx.1,
      (fun n ↦ by rw [hI.dpow_mul hx.1, hI'.dpow_mul hx.1, hx.2])⟩

theorem mem_dpEqualizer_iff {A : Type*} [CommSemiring A] {I : Ideal A} (hI hI' : DividedPowers I)
    {x : A} : x ∈ dpEqualizer hI hI' ↔ x ∈ I ∧ ∀ n : ℕ, hI.dpow n x = hI'.dpow n x := by
  simp only [dpEqualizer, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]

theorem dpEqualizer_is_dp_ideal_left {A : Type*} [CommSemiring A] {I : Ideal A}
    (hI hI' : DividedPowers I) : DividedPowers.IsSubDPIdeal hI (dpEqualizer hI hI') :=
  IsSubDPIdeal.mk (fun _ hx ↦ hx.1) (fun _ hn x hx ↦ ⟨hI.dpow_mem hn hx.1,
    fun m ↦ by rw [hI.dpow_comp hn hx.1, hx.2, hx.2, hI'.dpow_comp hn hx.1]⟩)

theorem dpEqualizer_is_dp_ideal_right {A : Type*} [CommSemiring A] {I : Ideal A}
    (hI hI' : DividedPowers I) : DividedPowers.IsSubDPIdeal hI' (dpEqualizer hI hI') :=
  IsSubDPIdeal.mk (fun _ hx ↦ hx.1) (fun _ hn x hx ↦ ⟨hI'.dpow_mem hn hx.1, fun m ↦ by
    rw [← hx.2, hI.dpow_comp hn hx.1, hx.2, hx.2, hI'.dpow_comp hn hx.1]⟩)

open Ideal

theorem le_equalizer_of_dp_morphism {A : Type*} [CommSemiring A] {I : Ideal A}
    (hI : DividedPowers I) {B : Type*} [CommSemiring B] (f : A →+* B) {K : Ideal B}
    (hI_le_K : Ideal.map f I ≤ K) (hK hK' : DividedPowers K) (hIK : IsDPMorphism hI hK f)
    (hIK' : IsDPMorphism hI hK' f) : Ideal.map f I ≤ dpEqualizer hK hK' := by
  rw [Ideal.map, span_le]
  rintro b ⟨a, ha, rfl⟩
  exact ⟨hI_le_K (mem_map_of_mem f ha), fun n ↦ by rw [hIK.2 a ha, hIK'.2 a ha]⟩

/-- If there is a dp-structure on I(A/J) such that the quotient map is
   a dp-morphism, then J ⊓ I is a sub-dp-ideal of I -/
def interQuot {A : Type*} [CommRing A] {I : Ideal A} {hI : DividedPowers I} {J : Ideal A}
    {hJ : DividedPowers (I.map (Ideal.Quotient.mk J))} {φ : DPMorphism hI hJ}
    (hφ : φ.toRingHom = Ideal.Quotient.mk J) :
  SubDPIdeal hI where
  carrier    := J ⊓ I
  isSubideal := by simp only [ge_iff_le, inf_le_right]
  dpow_mem   := fun _ hn a ⟨haJ, haI⟩ ↦ by
    refine ⟨?_, hI.dpow_mem hn haI⟩
    rw [SetLike.mem_coe, ← Quotient.eq_zero_iff_mem, ← hφ, ← φ.dpow_comp a haI]
    suffices ha0 : φ.toRingHom a = 0 by
      rw [ha0, hJ.dpow_eval_zero hn]
    rw [hφ, Quotient.eq_zero_iff_mem]
    exact haJ

end Equalizer

section Quotient

/- Divided power structure on a quotient ring in two sorts:
* the case of a surjective ring_hom
* specific case for ideal.quotient.mk   -/
namespace Quotient

-- TODO : CommSemiring ?

variable {A : Type*} [CommRing A] {I : Ideal A} (hI : DividedPowers I)

section OfSurjective

namespace OfSurjective

-- Define divided powers on a quotient map via a surjective morphism
variable {B : Type*} [CommRing B] (f : A →+* B)

/- Tagged as noncomputable because it makes use of function.extend,
but under is_sub_pd_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on the codomain `B` of a surjective ring homomorphism
  from a ring `A` with divided powers `hI`.  -/
noncomputable def dpow : ℕ → B → B := fun n ↦
  Function.extend (fun a ↦ f a : I → B) (fun a ↦ f (hI.dpow n a) : I → B) 0

variable (hf : Function.Surjective f) (hIf : IsSubDPIdeal hI (RingHom.ker f ⊓ I))

variable {f}

/-- Divided powers on the quotient are compatible with quotient map -/
theorem dpow_apply' (hIf : IsSubDPIdeal hI (RingHom.ker f ⊓ I)) {n : ℕ} {a : A} (ha : a ∈ I) :
    dpow hI f n (f a) = f (hI.dpow n a) := by
  classical
  simp only [dpow, Function.extend_def]
  have h : ∃ (a_1 : I), f ↑a_1 = f a := by use ⟨a, ha⟩
  rw [dif_pos h, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]
  rw [IsSubDPIdeal_inf_iff] at hIf
  apply hIf _ ha
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, h.choose_spec]
  simp only [Submodule.coe_mem]

open Ideal

/-- When `f.ker ⊓ I` is a `sub_dp_ideal` of `I`, this is the induced divided power structure for
  the ideal `I.map f` of the target -/
noncomputable def dividedPowers : DividedPowers (I.map f) where
  dpow := dpow hI f
  dpow_null n {x} hx' := by
    classical
    rw [dpow, Function.extend_def, dif_neg, Pi.zero_apply]
    rintro ⟨⟨a, ha⟩, rfl⟩
    exact hx' (apply_coe_mem_map f I ⟨a, ha⟩)
  dpow_zero {x} hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hx
    rw [dpow_apply' hI hIf ha, hI.dpow_zero ha, map_one]
  dpow_one {x} hx := by
    obtain ⟨a, ha, hax⟩ := (mem_map_iff_of_surjective f hf).mp hx
    rw [← hax, dpow_apply' hI hIf ha, hI.dpow_one ha]
  dpow_mem {n x} hn hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hx
    rw [dpow_apply' hI hIf ha]
    exact mem_map_of_mem _ (hI.dpow_mem hn ha)
  dpow_add hx hy := by
    obtain ⟨a, ha, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hx
    obtain ⟨b, hb, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hy
    rw [← map_add, dpow_apply' hI hIf (I.add_mem ha hb), hI.dpow_add ha hb, map_sum,
      Finset.sum_congr rfl]
    · exact fun k _ ↦ by rw [dpow_apply' hI hIf ha, dpow_apply' hI hIf hb, ← _root_.map_mul]
  dpow_mul {n x y} hy := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, hb, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hy
    rw [dpow_apply' hI hIf hb, ← _root_.map_mul, ← map_pow,
      dpow_apply' hI hIf (mul_mem_left I a hb), hI.dpow_mul hb, _root_.map_mul]
  mul_dpow hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hIf ha]
    rw [← _root_.map_mul, hI.mul_dpow ha, _root_.map_mul, map_natCast]
  dpow_comp hn hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hIf, ha, hI.dpow_mem hn ha]
    rw [hI.dpow_comp hn ha, _root_.map_mul, map_natCast]

theorem dpow_def {n : ℕ} {x : B} : (dividedPowers hI hf hIf).dpow n x = dpow hI f n x := rfl

theorem dpow_apply {n : ℕ} {a : A} (ha : a ∈ I) :
    (dividedPowers hI hf hIf).dpow n (f a) = f (hI.dpow n a) := by
  rw [dpow_def, dpow_apply' hI hIf ha]

theorem IsDPMorphism : IsDPMorphism hI (dividedPowers hI hf hIf) f :=
  ⟨le_refl (Ideal.map f I), fun a ha ↦ by rw [dpow_apply hI hf hIf ha]⟩

theorem unique (hquot : DividedPowers (I.map f)) (hm : DividedPowers.IsDPMorphism hI hquot f) :
    hquot = dividedPowers hI hf hIf :=
  ext _ _ fun n x hx ↦ by
    obtain ⟨a, ha, rfl⟩ := (mem_map_iff_of_surjective f hf).mp hx
    rw [hm.2 a ha, dpow_apply hI hf hIf ha]

end OfSurjective

end OfSurjective

variable {J : Ideal A} (hIJ : IsSubDPIdeal hI (J ⊓ I))

/- Tagged as noncomputable because it makes use of function.extend,
but under is_sub_dp_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on `A ⧸ J` -/
noncomputable def dpow (J : Ideal A) : ℕ → A ⧸ J → A ⧸ J :=
  DividedPowers.Quotient.OfSurjective.dpow hI (Ideal.Quotient.mk J)

--TODO: think about whether this should be a lemma
private theorem IsSubDPIdeal_aux (hIJ : IsSubDPIdeal hI (J ⊓ I)) :
    IsSubDPIdeal hI (RingHom.ker (Ideal.Quotient.mk J) ⊓ I) := by
  simpa [Ideal.mk_ker] using hIJ

-- We wish for a better API to denote I.map (ideal.quotient.mk J) as I ⧸ J
/-- When `I ⊓ J` is a `sub_dp_ideal` of `I`, the divided power structure for the ideal `I(A⧸J)` of
  the quotient -/
noncomputable def dividedPowers : DividedPowers (I.map (Ideal.Quotient.mk J)) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers hI Ideal.Quotient.mk_surjective
    (IsSubDPIdeal_aux hI hIJ)

/-- Divided powers on the quotient are compatible with quotient map -/
theorem dpow_apply {n : ℕ} {a : A} (ha : a ∈ I) :
    (dividedPowers hI hIJ).dpow n (Ideal.Quotient.mk J a) = (Ideal.Quotient.mk J) (hI.dpow n a) :=
  DividedPowers.Quotient.OfSurjective.dpow_apply hI Ideal.Quotient.mk_surjective
    (IsSubDPIdeal_aux hI hIJ) ha

theorem isDPMorphism : hI.IsDPMorphism (dividedPowers hI hIJ) (Ideal.Quotient.mk J) :=
  DividedPowers.Quotient.OfSurjective.IsDPMorphism hI Ideal.Quotient.mk_surjective
    (IsSubDPIdeal_aux hI hIJ)

theorem unique (hquot : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (hm : DividedPowers.IsDPMorphism hI hquot (Ideal.Quotient.mk J)) :
    hquot = dividedPowers hI hIJ :=
  DividedPowers.Quotient.OfSurjective.unique hI Ideal.Quotient.mk_surjective
    (IsSubDPIdeal_aux hI hIJ) hquot hm

end Quotient

end Quotient

end DividedPowers
