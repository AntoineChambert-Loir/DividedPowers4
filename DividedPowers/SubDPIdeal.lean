/- ACL and MIdFF, Lean 2022 meeting at Icerm
! This file was ported from Lean 3 source module divided_powers.sub_pd_ideal
-/
import DividedPowers.Basic
import DividedPowers.BasicLemmas
import DividedPowers.DPMorphism
import Mathlib.RingTheory.Ideal.QuotientOperations

open Subtype

-- We should PR this lemma
theorem Submodule.iSup_eq_span' {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
  {ι : Sort _} (p : ι → Submodule R M) (h : ι → Prop) :
  (⨆ (i : ι) (_ : h i), p i) = Submodule.span R (⋃ (i : ι) (_ : h i), ↑(p i)) := by
  simp_rw [← Submodule.iSup_span, Submodule.span_eq]

-- Is any of this is in Mathlib? For Submodule, maybe?
namespace Subideal

variable {A : Type _} [CommSemiring A] {I : Ideal A}

def galoisCoinsertion :
  GaloisCoinsertion (fun J : { J : Ideal A // J ≤ I } => (J : Ideal A))
    (fun J : Ideal A => ⟨J ⊓ I, inf_le_right⟩) :=
  GaloisCoinsertion.monotoneIntro (fun _ _ h => mk_le_mk.mpr (inf_le_inf_right I h))
    (fun _ _ h => h) (fun _ => inf_le_left)
    (fun ⟨J, hJ⟩ => by simp only [ge_iff_le, mk.injEq, inf_eq_left, hJ])

instance : CompleteLattice { J : Ideal A // J ≤ I } :=
  GaloisCoinsertion.liftCompleteLattice galoisCoinsertion

theorem top_def : (⟨I, le_refl I⟩ : { J : Ideal A // J ≤ I }) = ⊤ :=
  eq_top_iff.mpr (⊤ : { J : Ideal A // J ≤ I }).property

theorem bot_def : (⟨⊥, bot_le⟩ : { J : Ideal A // J ≤ I }) = ⊥ := by rw [mk_bot]

theorem inf_def (J J' : { J : Ideal A // J ≤ I }) :
  (J ⊓ J' : { J : Ideal A // J ≤ I }) =
    ⟨(J : Ideal A) ⊓ (J' : Ideal A), inf_le_of_left_le J.2⟩ := by
  ext x
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, J.property h.left⟩⟩

-- `coe` has been replaced by `val`
example {α : Type _} (p : α → Prop) : { a // p a} → α := fun ⟨a, _⟩ => a

theorem sInf_def (S : Set { J : Ideal A // J ≤ I }) :
    (sInf S : { J : Ideal A // J ≤ I }) = ⟨sInf (val '' S) ⊓ I, inf_le_right⟩ := rfl

theorem sup_def (J J' : { J : Ideal A // J ≤ I }) :
    (J ⊔ J' : { J : Ideal A // J ≤ I }) = ⟨sInf {B | (J : Ideal A) ≤ B ∧ (J' : Ideal A) ≤ B},
      sInf_le_of_le ⟨J.2, J'.2⟩ (le_refl I)⟩ := by
  ext x
  refine ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, ?_⟩⟩
  rw [coe_mk, Submodule.mem_sInf] at h
  exact h I ⟨J.2, J'.2⟩

theorem sSup_def (S : Set { J : Ideal A // J ≤ I }) :
    (sSup S : { J : Ideal A // J ≤ I }) = ⟨sSup (val '' S) ⊓ I, inf_le_right⟩ := rfl

end Subideal

namespace DividedPowers

/-- The structure of a sub-dp-ideal of a dp-ideal -/
structure isSubDPIdeal {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)
    (J : Ideal A) : Prop where
  isSubIdeal : J ≤ I
  dpow_mem : ∀ n ≠ 0, ∀ j ∈ J, hI.dpow n j ∈ J
section isSubDPIdeal

variable {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)

theorem isSubDPIdeal.self : isSubDPIdeal hI I where
  isSubIdeal := le_rfl
  dpow_mem _ hn _ ha := hI.dpow_mem hn ha

def isSubDPIdeal.dividedPowers {J : Ideal A} (hJ : isSubDPIdeal hI J) [∀ x, Decidable (x ∈ J)] :
    DividedPowers J where
  dpow n x := if x ∈ J then hI.dpow n x else 0
  dpow_null {n x} hx := by simp only [if_neg hx]
  dpow_zero {x} hx := by simp only [if_pos hx]; exact hI.dpow_zero (hJ.isSubIdeal hx)
  dpow_one {x} hx := by simp only [if_pos hx]; exact hI.dpow_one (hJ.isSubIdeal hx)
  dpow_mem {n x} hn hx := by simp only [if_pos hx, hJ.dpow_mem n hn x hx]
  dpow_add n {x y} hx hy := by simp_rw [if_pos hx, if_pos hy, if_pos (Ideal.add_mem J hx hy),
    hI.dpow_add n (hJ.isSubIdeal hx) (hJ.isSubIdeal hy)]
  dpow_smul n {a x} hx := by
    simp only [if_pos hx, if_pos (Ideal.mul_mem_left J a hx), hI.dpow_smul n (hJ.isSubIdeal hx)]
  dpow_mul m n {x} hx := by simp only [if_pos hx, hI.dpow_mul m n (hJ.isSubIdeal hx)]
  dpow_comp m n {x} hn hx := by
    simp_rw [if_pos hx, if_pos (hJ.dpow_mem n hn x hx)]
    exact hI.dpow_comp m hn (hJ.isSubIdeal hx)

lemma isSubDPIdeal.dividedPowers.dpow_eq {J : Ideal A} (hJ : isSubDPIdeal hI J)
  [∀ x, Decidable (x ∈ J)] (n : ℕ) (a : A) :
  (isSubDPIdeal.dividedPowers hI hJ).dpow n a = if a ∈ J then hI.dpow n a else 0 := rfl

lemma isSubDPIdeal.dividedPowers.dpow_eq_of_mem {J : Ideal A} (hJ : isSubDPIdeal hI J)
  [∀ x, Decidable (x ∈ J)] (n : ℕ) {a : A} (ha : a ∈ J) :
  (isSubDPIdeal.dividedPowers hI hJ).dpow n a = hI.dpow n a := by rw [dpow_eq, if_pos ha]

-- TODO : CommSemiring ?

/-- The ideal J ⊓ I is a sub-dp-ideal of I,
  if and only if (on I) the divided powers have some compatiblity mod J.
  (The necessity was proved as a sanity check.) -/
theorem isSubDPIdeal_inf_iff
    {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    (J : Ideal A) :
    isSubDPIdeal hI (J ⊓ I) ↔
      ∀ (n : ℕ) (a b : A) (_ : a ∈ I) (_ : b ∈ I) (_ : a - b ∈ J),
        hI.dpow n a - hI.dpow n b ∈ J :=
  by
  refine' ⟨fun hIJ n a b ha hb hab => _, fun hIJ => _⟩
  · have hab' : a - b ∈ I := I.sub_mem ha hb
    rw [← add_sub_cancel b a, hI.dpow_add' n hb hab', Finset.range_succ,
      Finset.sum_insert Finset.not_mem_range_self, tsub_self, hI.dpow_zero hab', mul_one,
      add_sub_cancel_left]
    apply Ideal.sum_mem
    intro i hi
    apply SemilatticeInf.inf_le_left J I
    exact
      (J ⊓ I).smul_mem _
        (hIJ.dpow_mem (n - i) (ne_of_gt (Nat.sub_pos_of_lt (Finset.mem_range.mp hi))) _
          ⟨hab, hab'⟩)
  · refine' ⟨SemilatticeInf.inf_le_right J I, fun n hn a ha => ⟨_, hI.dpow_mem hn ha.right⟩⟩
    rw [← sub_zero (hI.dpow n a), ← hI.dpow_eval_zero hn]
    exact hIJ n a 0 ha.right I.zero_mem (J.sub_mem ha.left J.zero_mem)

/-- Lemma 3.6 of [BO] (Antoine) -/
theorem span_isSubDPIdeal_iff (S : Set A) (hS : S ⊆ I) :
  isSubDPIdeal hI (Ideal.span S) ↔
    ∀ (n : ℕ) (_ : n ≠ 0), ∀ s ∈ S, hI.dpow n s ∈ Ideal.span S := by
  constructor
  · -- trivial direction
    intro hhI h hn s hs
    apply hhI.dpow_mem h hn s (Ideal.subset_span hs)
  · -- interesting direction,
    intro hhI
    have hSI := Ideal.span_le.mpr hS
    apply isSubDPIdeal.mk hSI
    intro n hn z hz; revert n
    refine' Submodule.span_induction' _ _  _ _ hz
    ·-- case of elements of S
      intro s hs n hn;
      exact hhI n hn s hs
    ·-- case of 0
      intro n hn;
      rw [hI.dpow_eval_zero hn]; apply Ideal.zero_mem _
    · -- case of sum
      rintro x hxI y hyI hx hy n hn
      rw [hI.dpow_add' n (hSI hxI) (hSI hyI)]
      apply Submodule.sum_mem (Ideal.span S)
      intro m _
      by_cases hm0 : m = 0
      · rw [hm0]
        exact Ideal.mul_mem_left (Ideal.span S) _ (hy n hn)
      · exact Ideal.mul_mem_right _ (Ideal.span S) (hx m hm0)
    · -- case : product,
      intro a x hxI hx n hn
      simp only [Algebra.id.smul_eq_mul]
      rw [hI.dpow_smul n (hSI hxI)]
      exact Ideal.mul_mem_left (Ideal.span S) (a ^ n) (hx n hn)

theorem generated_dpow_isSubIdeal {S : Set A} (hS : S ⊆ I) :
    Ideal.span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} ≤ I := by
  rw [Ideal.span_le]
  rintro y ⟨n, hn, x, hx, hxy⟩
  rw [hxy]
  exact hI.dpow_mem hn (hS hx)

theorem isSubDPIdeal_sup {J K : Ideal A}
  (hJ : isSubDPIdeal hI J) (hK : isSubDPIdeal hI K) :
  isSubDPIdeal hI (J ⊔ K) :=
  by
  rw [← J.span_eq, ← K.span_eq, ← Ideal.span_union, span_isSubDPIdeal_iff]
  · intro n hn a ha
    cases' ha with ha ha
    . apply Ideal.span_mono Set.subset_union_left
      rw [J.span_eq]; exact hJ.2 n hn a ha
    . apply Ideal.span_mono Set.subset_union_right
      rw [K.span_eq]; exact hK.2 n hn a ha
  . rw [Set.union_subset_iff]; exact ⟨hJ.1, hK.1⟩


theorem Ideal.iSup_eq_span {ι : Type _} (p : ι → Ideal A) : (⨆ i, p i) = Ideal.span (⋃ i, ↑(p i)) :=
  Submodule.iSup_eq_span p


theorem isSubDPIdeal_iSup {ι : Type _}
  {J : ι → Ideal A} (hJ : ∀ i, isSubDPIdeal hI (J i)) :
  isSubDPIdeal hI (iSup J) := by
  rw [Ideal.iSup_eq_span]
  rw [span_isSubDPIdeal_iff]
  · rintro n hn a
    rw [Set.mem_iUnion]
    rintro ⟨i, ha⟩
    apply Ideal.span_mono (Set.subset_iUnion _ i)
    rw [Ideal.span_eq]; exact (hJ i).2 n hn a ha
  · rw [Set.iUnion_subset_iff]
    intro i; exact (hJ i).1

theorem isSubDPIdeal_map_of_isSubDPIdeal {B : Type _} [CommSemiring B] {J : Ideal B} (hJ : DividedPowers J)
    {f : A →+* B} (hf : isDPMorphism hI hJ f)
    (K : Ideal A) (hK : isSubDPIdeal hI K) :
    isSubDPIdeal hJ (Ideal.map f K) := by
  simp only [Ideal.map]
  rw [span_isSubDPIdeal_iff]
  rintro n hn y ⟨x, hx, rfl⟩
  rw [hf.2 n x (hK.1 hx)]
  apply Ideal.mem_map_of_mem
  exact hK.2 n hn x hx
  rintro y ⟨x, hx, rfl⟩
  exact hf.1 (Ideal.mem_map_of_mem f (hK.1 hx))

theorem isSubDPIdeal_map {B : Type _} [CommSemiring B] {J : Ideal B} (hJ : DividedPowers J)
    {f : A →+* B} (hf : isDPMorphism hI hJ f) :
    isSubDPIdeal hJ (Ideal.map f I) :=
  isSubDPIdeal_map_of_isSubDPIdeal hI hJ hf _ (isSubDPIdeal.self hI)

end isSubDPIdeal

/-- A `sub-dp-ideal` of `I` is a sub-ideal `J` of `I` such that for all `n ∈ ℕ ≥ 0` and all
  `j ∈ J`, `hI.dpow n j ∈ J`. -/
@[ext]
structure SubDPIdeal {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I) where
  carrier : Ideal A
  isSubIdeal : carrier ≤ I
  dpow_mem : ∀ (n : ℕ) (_ : n ≠ 0), ∀ j ∈ carrier, hI.dpow n j ∈ carrier

namespace SubDPIdeal

variable {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)

def mk' (J : Ideal A) (hJ : hI.isSubDPIdeal J) : hI.SubDPIdeal :=
  ⟨J, hJ.1, hJ.2⟩

instance : SetLike (SubDPIdeal hI) A where
  coe s := s.carrier
  coe_injective' p q h := by
    rw [SetLike.coe_set_eq] at h
    cases p ; cases q ; congr

@[coe]
def toIdeal (J : hI.SubDPIdeal) : Ideal A := J.carrier

instance : CoeOut (hI.SubDPIdeal) (Ideal A) :=
  ⟨fun J => J.toIdeal⟩

theorem coe_def (J : SubDPIdeal hI) : J.toIdeal = J.carrier :=
  rfl

@[simp]
theorem memCarrier {s : SubDPIdeal hI} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

variable {hI}
def toIsSubDPIdeal (J : SubDPIdeal hI) : isSubDPIdeal hI J.carrier := {
  isSubIdeal := J.isSubIdeal,
  dpow_mem := J.dpow_mem }

def isSubDPIdeal.mk' (J : Ideal A) (hJ : isSubDPIdeal hI J) : SubDPIdeal hI :=
{ carrier := J,
  isSubIdeal := hJ.isSubIdeal,
  dpow_mem := hJ.dpow_mem }

lemma IsSubDPIdeal_of_SubDPIdeal (J : SubDPIdeal hI) :
  isSubDPIdeal.mk' J.carrier J.toIsSubDPIdeal = J := rfl

lemma SubDPIdeal_of_IsSubDPIdeal {J  : Ideal A} (hJ : isSubDPIdeal hI J) :
  (isSubDPIdeal.mk' J hJ).toIsSubDPIdeal = hJ := rfl

/-- If J is an ideal of A, then J ⬝ I is a sub-dp-ideal of I. (Berthelot, 1.6.1 (i)) -/
def prod (J : Ideal A) : SubDPIdeal hI
    where
  carrier := I • J
  isSubIdeal := Ideal.mul_le_right
  dpow_mem n hn x hx := by
    revert n
    apply @Submodule.smul_induction_on' A A _ _ _ I J _ hx
    · -- mul
      intro a ha b hb n hn
      rw [Algebra.id.smul_eq_mul, smul_eq_mul, mul_comm a b, hI.dpow_smul n ha, mul_comm]
      exact Submodule.mul_mem_mul (J.pow_mem_of_mem hb n (zero_lt_iff.mpr hn)) (hI.dpow_mem hn ha)
    · -- add
      intro x hx y hy hx' hy' n hn
      rw [hI.dpow_add' n (Ideal.mul_le_right hx) (Ideal.mul_le_right hy)]
      apply Submodule.sum_mem (I • J)
      intro k _
      by_cases hk0 : k = 0
      · rw [hk0]; apply Ideal.mul_mem_left (I • J); exact hy' _ hn
      · apply Ideal.mul_mem_right _ (I • J); exact hx' k hk0

section CompleteLattice

instance : CoeOut (SubDPIdeal hI) { J : Ideal A // J ≤ I } :=
  ⟨fun J => ⟨J.carrier, J.isSubIdeal⟩⟩

instance : LE (SubDPIdeal hI) :=
  ⟨fun J J' => J.carrier ≤ J'.carrier⟩

theorem le_iff {J J' : SubDPIdeal hI} : J ≤ J' ↔ J.carrier ≤ J'.carrier := Iff.rfl

instance : LT (SubDPIdeal hI) :=
  ⟨fun J J' => J.carrier < J'.carrier⟩

theorem lt_iff {J J' : SubDPIdeal hI} : J < J' ↔ J.carrier < J'.carrier := Iff.rfl

/-- I is a sub-dp-ideal ot itself. -/
instance : Top (SubDPIdeal hI) :=
  ⟨{  carrier := I
      isSubIdeal := le_refl _
      dpow_mem := fun _ hn _x hx => hI.dpow_mem hn hx }⟩

instance inhabited : Inhabited hI.SubDPIdeal := ⟨⊤⟩

/-- (0) is a sub-dp-ideal ot the dp-ideal I. -/
instance : Bot (SubDPIdeal hI) :=
  ⟨{  carrier := ⊥
      isSubIdeal := bot_le
      dpow_mem := fun n hn x hx => by
        rw [Ideal.mem_bot.mp hx, hI.dpow_eval_zero hn, Ideal.mem_bot] }⟩

--Section 1.8 of [B]
-- The intersection of two sub-dp-ideals is a sub-dp-ideal.
instance : Inf (SubDPIdeal hI) :=
  ⟨fun J J' =>
    { carrier := J.carrier ⊓ J'.carrier
      isSubIdeal := fun _ hx => J.isSubIdeal hx.1
      dpow_mem := fun n hn x hx =>
        ⟨J.dpow_mem n hn x hx.1, J'.dpow_mem n hn x hx.2⟩ }⟩

theorem inf_carrier_def (J J' : SubDPIdeal hI) : (J ⊓ J').carrier = J.carrier ⊓ J'.carrier := rfl

instance : InfSet (SubDPIdeal hI) :=
  ⟨fun S =>
    { carrier := ⨅ s ∈ Insert.insert ⊤ S, (s : hI.SubDPIdeal).carrier
      isSubIdeal := fun x hx => by
        simp only [Ideal.mem_iInf] at hx
        exact hx ⊤ (Set.mem_insert ⊤ S)
      dpow_mem := fun n hn x hx =>
        by
        simp only [Ideal.mem_iInf] at hx ⊢
        intro s hs
        exact s.dpow_mem n hn x (hx s hs) }⟩

theorem sInf_carrier_def (S : Set (SubDPIdeal hI)) :
    (sInf S).carrier = ⨅ s ∈ Insert.insert ⊤ S, (s : hI.SubDPIdeal).carrier := rfl

instance : Sup (SubDPIdeal hI) :=
  ⟨fun J J' =>
    isSubDPIdeal.mk' (J.carrier ⊔ J'.carrier) (isSubDPIdeal_sup hI J.toIsSubDPIdeal J'.toIsSubDPIdeal)⟩

theorem sup_carrier_def (J J' : SubDPIdeal hI) : (J ⊔ J').carrier = J ⊔ J' := rfl

instance : SupSet (SubDPIdeal hI) :=
  ⟨fun S =>
    isSubDPIdeal.mk' (sSup ((fun J => J.carrier) '' S)) <|
      by
      have h : (⋃ (i : Ideal A) (_ : i ∈ (fun J => J.carrier) '' S), ↑i) ⊆ (I : Set A) :=
        by
        rintro a ⟨-, ⟨J, rfl⟩, haJ⟩
        rw [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at haJ
        obtain ⟨J', hJ'⟩ := (Set.mem_image _ _ _).mp haJ.1
        rw [← hJ'.2] at haJ
        exact J'.isSubIdeal haJ.2
      rw [sSup_eq_iSup, Submodule.iSup_eq_span', Ideal.submodule_span_eq,
        span_isSubDPIdeal_iff hI _ h]
      rintro n hn x ⟨T, hT, hTx⟩
      obtain ⟨J, hJ⟩ := hT
      rw [← hJ] at hTx
      obtain ⟨J', ⟨⟨hJ', rfl⟩, h'⟩⟩ := hTx
      apply Ideal.subset_span
      apply Set.mem_biUnion hJ'
      obtain ⟨K, hKS, rfl⟩ := hJ'
      exact K.dpow_mem n hn x h'⟩

theorem sSup_carrier_def (S : Set (SubDPIdeal hI)) :
    (sSup S).carrier = sSup ((toIdeal hI) '' S) := rfl

instance : CompleteLattice (SubDPIdeal hI) := by
  refine' Function.Injective.completeLattice
    (fun J : SubDPIdeal hI => (J : { J : Ideal A // J ≤ I }))
    (fun J J' h => by simpa only [SubDPIdeal.ext_iff, Subtype.mk.injEq] using h)
    (fun J J' => by rw [Subideal.sup_def] ; rfl)
    (fun J J' => by rw [Subideal.inf_def] ; rfl)
    _ _ (by rw [← Subideal.top_def] ; rfl ) (by rw [← Subideal.bot_def] ; rfl)
  · intro S
    conv_rhs => rw [iSup]
    rw [Subideal.sSup_def, Subtype.ext_iff]
    dsimp
    rw [sSup_carrier_def, sSup_image, sSup_image, iSup_range]
    have : ∀ J : hI.SubDPIdeal,
      ((⨆ (_ : J ∈ S), (J : { B : Ideal A // B ≤ I }) : { B : Ideal A // B ≤ I }) : Ideal A) =
        ⨆ (_ : J ∈ S), (J : Ideal A) := by
      intro J
      dsimp
      by_cases hJ : J ∈ S
      · simp [ciSup_pos hJ, ciSup_pos hJ]
      · simp only [hJ, iSup_false, coe_eq_bot_iff, bot_le]
    simp_rw [this]
    ext a
    refine' ⟨fun ha => ⟨ha, _⟩, fun ha => ha.1⟩
    apply (Submodule.mem_iSup _).mp ha I
    intro J
    by_cases hJ : J ∈ S
    · rw [ciSup_pos hJ]; exact J.isSubIdeal
    · simp only [hJ, iSup_false, bot_le]
  · intro S
    conv_rhs => rw [iInf]
    rw [Subideal.sInf_def, Subtype.ext_iff]
    dsimp
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
def generated (S : Set A) : SubDPIdeal hI :=
  sInf {J : SubDPIdeal hI | S ⊆ J.carrier}

/-- The sub-dp-ideal of I generated by the family `hI.dpow n x`,
  where `n ≠ 0` and `x ∈ S`. -/
def generatedDpow {S : Set A} (hS : S ⊆ I) : SubDPIdeal hI where
  carrier := Ideal.span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x}
  isSubIdeal := hI.generated_dpow_isSubIdeal hS
  dpow_mem n hn z hz := by
    have hSI := hI.generated_dpow_isSubIdeal hS
    revert n
    refine' Submodule.span_induction' _ _ _ _ hz
    · -- Elements of S
      rintro y ⟨m, hm, x, hxS, hxy⟩ n hn
      rw [hxy, hI.dpow_comp n hm (hS hxS)]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n * m, mul_ne_zero hn hm, x, hxS, rfl⟩)
    · -- Zero
      intro n hn
      rw [hI.dpow_eval_zero hn]; exact Ideal.zero_mem _
    · intro x hx y hy hx_pow hy_pow n hn
      rw [hI.dpow_add' n (hSI hx) (hSI hy)]
      apply Submodule.sum_mem (Ideal.span _)
      intro m _
      by_cases hm0 : m = 0
      · rw [hm0]; exact Ideal.mul_mem_left (Ideal.span _) _ (hy_pow n hn)
      · exact Ideal.mul_mem_right _ (Ideal.span _) (hx_pow m hm0)
    · intro a x hx hx_pow n hn
      rw [smul_eq_mul, hI.dpow_smul n (hSI hx)]
      exact Ideal.mul_mem_left (Ideal.span _) (a ^ n) (hx_pow n hn)

theorem generatedDpow_carrier {S : Set A} (hS : S ⊆ I) :
    (generatedDpow hI hS).carrier =
      Ideal.span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} := rfl

theorem le_generatedDpow {S : Set A} (hS : S ⊆ I) : S ⊆ (generatedDpow hI hS).carrier := fun x hx =>
  Ideal.subset_span ⟨1, one_ne_zero, x, hx, by rw [hI.dpow_one (hS hx)]⟩

theorem generated_dpow_le (S : Set A) (J : SubDPIdeal hI) (hSJ : S ⊆ J.carrier) :
    Ideal.span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} ≤
      J.carrier := by
  rw [Ideal.span_le]
  rintro y ⟨n, hn, x, hx, hxy⟩
  rw [hxy]
  exact J.dpow_mem n hn x (hSJ hx)

theorem generated_carrier_eq {S : Set A} (hS : S ⊆ I) :
    (generated hI S).carrier =
      Ideal.span {y : A | ∃ (n : ℕ) (_ : n ≠ 0) (x : A) (_ : x ∈ S), y = hI.dpow n x} := by
  simp only [generated, sInf_carrier_def]
  apply le_antisymm
  · have h : generatedDpow hI hS ∈ insert ⊤ {J : hI.SubDPIdeal | S ⊆ ↑J.carrier} :=
      by
      apply Set.mem_insert_of_mem
      simp only [Set.mem_setOf_eq, generatedDpow_carrier]
      exact le_generatedDpow hI hS
    refine' sInf_le_of_le ⟨generatedDpow hI hS, _⟩ (le_refl _)
    simp only [h, ciInf_pos]
    rfl
  · rw [le_iInf₂_iff]
    rintro J hJ
    refine' generated_dpow_le hI S J _
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff] at hJ
    cases' hJ with hJI hJS
    · rw [hJI]; exact hS
    · exact hJS

end Generated

end SubDPIdeal

section Ker

-- TODO : CommSemiring ?

variable {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
  {B : Type _} [CommRing B] {J : Ideal B} (hJ : DividedPowers J)

theorem isSubDPIdeal_ker {f : A →+* B} (hf : isDPMorphism hI hJ f) :
    isSubDPIdeal hI (RingHom.ker f ⊓ I) := by
  rw [isSubDPIdeal_inf_iff]
  simp only [isDPMorphism] at hf
  intro n a b ha hb
  simp only [RingHom.sub_mem_ker_iff]
  rw [← hf.2 n a ha, ← hf.2 n b hb]
  exact congr_arg _

def DPMorphism.ker (f : dpMorphism hI hJ) : SubDPIdeal hI where
  carrier := RingHom.ker f.toRingHom ⊓ I
  isSubIdeal := inf_le_right
  dpow_mem n hn a :=
    by
    simp only [Ideal.mem_inf, and_imp, RingHom.mem_ker]
    intro ha ha'
    rw [← f.isDPMorphism.2 n a ha', ha]
    exact ⟨dpow_eval_zero hJ hn, hI.dpow_mem hn ha'⟩

end Ker

section Equalizer

variable {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)

/- TODO : The set of elements where two divided
powers coincide is the largest ideal which is a sub-dp-ideal in both -/
def dpEqualizer {A : Type _} [CommSemiring A] {I : Ideal A} (hI hI' : DividedPowers I) : Ideal A
    where
  carrier := {a ∈ I | ∀ n : ℕ, hI.dpow n a = hI'.dpow n a}
  add_mem' {a b} ha hb := by
    apply And.intro (Ideal.add_mem I ha.1 hb.1)
    intro n
    rw [hI.dpow_add n ha.1 hb.1, hI'.dpow_add n ha.1 hb.1]
    apply Finset.sum_congr rfl
    intro k _
    rw [ha.2, hb.2]
  zero_mem' := by
    simp only [Set.mem_sep_iff, SetLike.mem_coe]
    apply And.intro (Ideal.zero_mem I)
    intro n
    by_cases hn : n = 0
    rw [hn, hI.dpow_zero (zero_mem I), hI'.dpow_zero (zero_mem I)]
    rw [hI.dpow_eval_zero hn, hI'.dpow_eval_zero hn]
  smul_mem' a x hx := by
    simp only [Set.mem_sep_iff, SetLike.mem_coe] at hx ⊢
    simp only [Algebra.id.smul_eq_mul]
    constructor
    refine' Ideal.mul_mem_left I a hx.1
    intro n
    rw [hI.dpow_smul n hx.1]; rw [hI'.dpow_smul n hx.1]
    rw [hx.2]

theorem mem_dpEqualizer_iff {A : Type _} [CommSemiring A] {I : Ideal A} (hI hI' : DividedPowers I)
    {x : A} : x ∈ dpEqualizer hI hI' ↔ x ∈ I ∧ ∀ n : ℕ, hI.dpow n x = hI'.dpow n x := by
  simp only [dpEqualizer, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

theorem dpEqualizer_is_dp_ideal_left {A : Type _} [CommSemiring A] {I : Ideal A}
    (hI hI' : DividedPowers I) : DividedPowers.isSubDPIdeal hI (dpEqualizer hI hI') :=
  by
  apply isSubDPIdeal.mk
  · intro x hx
    rw [mem_dpEqualizer_iff] at hx
    exact hx.1
  · intro n hn x hx
    rw [mem_dpEqualizer_iff] at hx ⊢
    constructor
    apply hI.dpow_mem hn hx.1
    intro m
    rw [hI.dpow_comp m hn hx.1, hx.2, hx.2, hI'.dpow_comp m hn hx.1]

theorem dpEqualizer_is_dp_ideal_right {A : Type _} [CommSemiring A] {I : Ideal A}
    (hI hI' : DividedPowers I) : DividedPowers.isSubDPIdeal hI' (dpEqualizer hI hI') := by
  apply isSubDPIdeal.mk
  · intro x hx
    rw [mem_dpEqualizer_iff] at hx
    exact hx.1
  · intro n hn x hx
    rw [mem_dpEqualizer_iff] at hx ⊢
    constructor
    apply hI'.dpow_mem hn hx.1
    intro m
    rw [← hx.2, hI.dpow_comp m hn hx.1, hx.2, hx.2, hI'.dpow_comp m hn hx.1]

theorem le_equalizer_of_dp_morphism {A : Type _} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type _} [CommSemiring B] (f : A →+* B) {K : Ideal B} (hI_le_K : Ideal.map f I ≤ K)
    (hK hK' : DividedPowers K) (hIK : isDPMorphism hI hK f) (hIK' : isDPMorphism hI hK' f) :
    Ideal.map f I ≤ dpEqualizer hK hK' := by
  rw [Ideal.map]; rw [Ideal.span_le]
  rintro b ⟨a, ha, rfl⟩
  simp only [SetLike.mem_coe] at ha ⊢
  rw [mem_dpEqualizer_iff]
  constructor
  apply hI_le_K; exact Ideal.mem_map_of_mem f ha
  simp only [isDPMorphism, Ideal.map_id, RingHom.id_apply] at hIK hIK'
  intro n
  rw [hIK.2 n a ha, hIK'.2 n a ha]

/-- If there is a dp-structure on I(A/J) such that the quotient map is
   a dp-morphism, then J ⊓ I is a sub-dp-ideal of I -/
def interQuot {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    (J : Ideal A) (hJ : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (φ : dpMorphism hI hJ) (hφ : φ.toRingHom = Ideal.Quotient.mk J) :
  SubDPIdeal hI where
  carrier := J ⊓ I
  isSubIdeal := by simp only [ge_iff_le, inf_le_right]
  dpow_mem := fun n hn a ⟨haJ, haI⟩ => by
    refine' ⟨_, hI.dpow_mem hn haI⟩
    rw [SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem, ← hφ, ← φ.dpow_comp n a haI]
    suffices ha0 : φ.toRingHom a = 0 by
      rw [ha0]
      exact hJ.dpow_eval_zero hn
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact haJ

end Equalizer

section Quotient

/- Divided power structure on a quotient ring in two sorts:
* the case of a surjective ring_hom
* specific case for ideal.quotient.mk   -/
namespace Quotient

-- TODO : CommSemiring ?

variable {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)

section OfSurjective

namespace OfSurjective

-- Define divided powers on a quotient map via a surjective morphism
variable {B : Type _} [CommRing B] (f : A →+* B) (hf : Function.Surjective f)

/- Tagged as noncomputable because it makes use of function.extend,
but under is_sub_pd_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on B -/
noncomputable def dpow : ℕ → B → B := fun n =>
  Function.extend (fun a => f a : I → B) (fun a => f (hI.dpow n a) : I → B) 0

variable (hIf : isSubDPIdeal hI (RingHom.ker f ⊓ I))

variable {f}

/-- Divided powers on the quotient are compatible with quotient map -/
theorem dpow_apply' (hIf : isSubDPIdeal hI (RingHom.ker f ⊓ I)) {n : ℕ} {a : A} (ha : a ∈ I) :
    dpow hI f n (f a) = f (hI.dpow n a) := by
  classical
  simp only [dpow, Function.extend_def]
  have h : ∃ (a_1 : I), f ↑a_1 = f a := by use ⟨a, ha⟩
  rw [dif_pos h]
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]
  rw [isSubDPIdeal_inf_iff] at hIf
  apply hIf n _ a _ ha
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  rw [h.choose_spec]
  simp only [Submodule.coe_mem]

/--
When `f.ker ⊓ I` is a `sub_dp_ideal` of `I`, the dpow map for the ideal `I.map f` of the target -/
noncomputable def dividedPowers : DividedPowers (I.map f) where
  dpow := dpow hI f
  dpow_null n {x} hx' := by
    classical
    simp only [dpow, Function.extend_def]
    rw [dif_neg]
    simp only [Pi.zero_apply]
    intro h
    obtain ⟨⟨a, ha⟩, rfl⟩ := h
    apply hx'
    exact Ideal.apply_coe_mem_map f I ⟨a, ha⟩
  dpow_zero {x} hx := by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [dpow_apply' hI hIf ha, hI.dpow_zero ha, map_one]
  dpow_one {x} hx := by
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [← hax, dpow_apply' hI hIf ha, hI.dpow_one ha]
  dpow_mem {n x} hn hx := by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hIf ha]
    apply Ideal.mem_map_of_mem _ (hI.dpow_mem hn ha)
  dpow_add n x y hx hy := by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hy
    rw [← map_add, dpow_apply' hI hIf (I.add_mem ha hb), hI.dpow_add n ha hb, map_sum,
      Finset.sum_congr rfl]
    · intro k _
      rw [dpow_apply' hI hIf ha, dpow_apply' hI hIf hb, ← map_mul]
  dpow_smul n x y hy := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hy
    rw [dpow_apply' hI hIf hb, ← map_mul, ← map_pow,
      dpow_apply' hI hIf (Ideal.mul_mem_left I a hb), hI.dpow_smul n hb, map_mul]
  dpow_mul m n x hx := by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hIf ha]
    rw [← map_mul, hI.dpow_mul m n ha, map_mul, map_natCast]
  dpow_comp m n x hn hx := by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hIf, ha, hI.dpow_mem hn ha]
    rw [hI.dpow_comp m hn ha, map_mul, map_natCast]

theorem dpow_def {n : ℕ} {x : B} : (dividedPowers hI hf hIf).dpow n x = dpow hI f n x := rfl

theorem dpow_apply {n : ℕ} {a : A} (ha : a ∈ I) :
    (dividedPowers hI hf hIf).dpow n (f a) = f (hI.dpow n a) := by
  rw [dpow_def, dpow_apply' hI hIf ha]

theorem isDPMorphism : isDPMorphism hI (dividedPowers hI hf hIf) f := by
  constructor
  exact le_refl (Ideal.map f I)
  intro n a ha; rw [dpow_apply hI hf hIf ha]

theorem unique (hquot : DividedPowers (I.map f)) (hm : DividedPowers.isDPMorphism hI hquot f) :
    hquot = dividedPowers hI hf hIf :=
  eq_of_eq_on_ideal _ _ fun n x hx => by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [hm.2 n a ha, dpow_apply hI hf hIf ha]

end OfSurjective

end OfSurjective

variable {J : Ideal A} (hIJ : isSubDPIdeal hI (J ⊓ I))

/- Tagged as noncomputable because it makes use of function.extend,
but under is_sub_dp_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on A ⧸ J -/
noncomputable def dpow (J : Ideal A) : ℕ → A ⧸ J → A ⧸ J :=
  DividedPowers.Quotient.OfSurjective.dpow hI (Ideal.Quotient.mk J)

--TODO: think about whether this should be a lemma
private theorem isSubDPIdeal_aux (hIJ : isSubDPIdeal hI (J ⊓ I)) :
    isSubDPIdeal hI (RingHom.ker (Ideal.Quotient.mk J) ⊓ I) := by
  simpa [Ideal.mk_ker] using hIJ

-- We wish for a better API to denote I.map (ideal.quotient.mk J) as I ⧸ J
/-- When `I ⊓ J` is a `sub_dp_ideal` of `I`, the dpow map for the ideal `I(A⧸J)` of the quotient -/
noncomputable def dividedPowers : DividedPowers (I.map (Ideal.Quotient.mk J)) := by
  apply DividedPowers.Quotient.OfSurjective.dividedPowers hI Ideal.Quotient.mk_surjective
    (isSubDPIdeal_aux hI hIJ)

/-- Divided powers on the quotient are compatible with quotient map -/
theorem dpow_apply {n : ℕ} {a : A} (ha : a ∈ I) :
    (dividedPowers hI hIJ).dpow n (Ideal.Quotient.mk J a) = (Ideal.Quotient.mk J) (hI.dpow n a) :=
  DividedPowers.Quotient.OfSurjective.dpow_apply hI Ideal.Quotient.mk_surjective
    (isSubDPIdeal_aux hI hIJ) ha

theorem isDPMorphism : DividedPowers.isDPMorphism hI (dividedPowers hI hIJ)
  (Ideal.Quotient.mk J) :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism hI Ideal.Quotient.mk_surjective
    (isSubDPIdeal_aux hI hIJ)

theorem unique (hquot : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (hm : DividedPowers.isDPMorphism hI hquot (Ideal.Quotient.mk J)) :
    hquot = dividedPowers hI hIJ :=
  DividedPowers.Quotient.OfSurjective.unique hI Ideal.Quotient.mk_surjective (isSubDPIdeal_aux hI hIJ)
    hquot hm

end Quotient

end Quotient

end DividedPowers
