/- ACL and MIdFF, Lean 2022 meeting at Icerm 
! This file was ported from Lean 3 source module divided_powers.sub_pd_ideal
-/
import DividedPowers.Basic
import DividedPowers.BasicLemmas

#check ConditionallyCompleteLattice
open Subtype

-- We should PR this lemma
theorem Submodule.iSup_eq_span' {R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
  {ι : Sort _} (p : ι → Submodule R M) (h : ι → Prop) :
  (⨆ (i : ι) (_ : h i), p i) = Submodule.span R (⋃ (i : ι) (_ : h i), ↑(p i)) := by
  simp_rw [← Submodule.iSup_span, Submodule.span_eq]
#align submodule.supr_eq_span' Submodule.iSup_eq_span'

namespace Subideal

variable {A : Type _} [CommRing A] {I : Ideal A}

def galoisCoinsertion :
  GaloisCoinsertion 
    (fun J : { J : Ideal A // J ≤ I } => (J : Ideal A)) 
    (fun J : Ideal A => ⟨J ⊓ I, inf_le_right⟩) :=
  GaloisCoinsertion.monotoneIntro 
    (fun J J' h => mk_le_mk.mpr (inf_le_inf_right I h))
    (fun J J' h => h) 
    (fun J => inf_le_left) 
    (fun ⟨J, hJ⟩ => by simp only [ge_iff_le, mk.injEq, inf_eq_left]; exact hJ)
#align subideal.galois_coinsertion Subideal.galoisCoinsertion

instance : CompleteLattice { J : Ideal A // J ≤ I } :=
  GaloisCoinsertion.liftCompleteLattice galoisCoinsertion

theorem top_def : (⟨I, le_refl I⟩ : { J : Ideal A // J ≤ I }) = ⊤ :=
  eq_top_iff.mpr (⊤ : { J : Ideal A // J ≤ I }).property
#align subideal.top_def Subideal.top_def

theorem bot_def : (⟨⊥, bot_le⟩ : { J : Ideal A // J ≤ I }) = ⊥ := by rw [mk_bot]
#align subideal.bot_def Subideal.bot_def

theorem inf_def (J J' : { J : Ideal A // J ≤ I }) :
  (J ⊓ J' : { J : Ideal A // J ≤ I }) = 
    ⟨(J : Ideal A) ⊓ (J' : Ideal A), inf_le_of_left_le J.2⟩ := by 
  ext x
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, J.property h.left⟩⟩
#align subideal.inf_def Subideal.inf_def

-- `coe` has been replaced by `val`
example {α : Type _} (p : α → Prop) : { a // p a} → α := fun ⟨a, _⟩ => a

theorem sInf_def (S : Set { J : Ideal A // J ≤ I }) :
  (sInf S : { J : Ideal A // J ≤ I }) = 
    ⟨sInf (val '' S) ⊓ I, inf_le_right⟩ := by
  ext x
  rfl
#align subideal.Inf_def Subideal.sInf_def

theorem sup_def (J J' : { J : Ideal A // J ≤ I }) :
    (J ⊔ J' : { J : Ideal A // J ≤ I }) =
      ⟨sInf {B | (J : Ideal A) ≤ B ∧ (J' : Ideal A) ≤ B}, sInf_le_of_le ⟨J.2, J'.2⟩ (le_refl I)⟩ :=
  by
  ext x
  refine' ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, _⟩⟩
  rw [coe_mk, Submodule.mem_sInf] at h 
  exact h I ⟨J.2, J'.2⟩
#align subideal.sup_def Subideal.sup_def

theorem sSup_def (S : Set { J : Ideal A // J ≤ I }) :
    (sSup S : { J : Ideal A // J ≤ I }) = ⟨sSup (val '' S) ⊓ I, inf_le_right⟩ := by
  ext x
  rfl
#align subideal.Sup_def Subideal.sSup_def

end Subideal

namespace DividedPowers

/-- The structure of a sub-pd-ideal of a pd-ideal -/
structure IsSubPdIdeal {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    (J : Ideal A) : Prop where
  is_sub_ideal : J ≤ I
  dpow_mem_ideal : ∀ n (_ : n ≠ 0), ∀ j ∈ J, hI.dpow n j ∈ J
#align divided_powers.is_sub_pd_ideal DividedPowers.IsSubPdIdeal

section IsSubPdIdeal

variable {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)

def IsSubPdIdeal.dividedPowers {J : Ideal A} (hJ : IsSubPdIdeal hI J) [∀ x, Decidable (x ∈ J)] :
    DividedPowers J where
  dpow n x := if x ∈ J then hI.dpow n x else 0
  dpow_null {n x} hx := by dsimp; rw [if_neg hx]
  dpow_zero {x} hx := by dsimp ; rw [if_pos hx] ; exact hI.dpow_zero (hJ.is_sub_ideal hx)
  dpow_one {x} hx := by dsimp ; rw [if_pos hx] ; exact hI.dpow_one (hJ.is_sub_ideal hx)
  dpow_mem {n x} hn hx := by dsimp ; rw [if_pos hx] ; exact hJ.dpow_mem_ideal n hn x hx
  dpow_add n {x y} hx hy := by
    simp_rw [if_pos hx, if_pos hy, if_pos (Ideal.add_mem J hx hy)] <;>
      rw [hI.dpow_add n (hJ.is_sub_ideal hx) (hJ.is_sub_ideal hy)]
  dpow_smul n a x hx := by
    dsimp
    rw [if_pos hx, if_pos (Ideal.mul_mem_left J a hx), hI.dpow_smul n (hJ.is_sub_ideal hx)]
  dpow_mul m n x hx := by simp only [if_pos hx, hI.dpow_mul m n (hJ.is_sub_ideal hx)]
  dpow_comp m n x hn hx := by
    dsimp
    simp_rw [if_pos hx]
    rw [if_pos (hJ.dpow_mem_ideal n hn x hx)]
    exact hI.dpow_comp m hn (hJ.is_sub_ideal hx)
#align divided_powers.is_sub_pd_ideal.divided_powers DividedPowers.IsSubPdIdeal.dividedPowers

/-- The ideal J ⊓ I is a sub-pd-ideal of I, if and only if (on I) the divided powers have some 
  compatiblity mod J. (The necessity was proved as a sanity check.) -/
theorem isSubPdIdeal_inf_iff (J : Ideal A) :
    IsSubPdIdeal hI (J ⊓ I) ↔
      ∀ (n : ℕ) (a b : A) (ha : a ∈ I) (hb : b ∈ I) (hab : a - b ∈ J),
        hI.dpow n a - hI.dpow n b ∈ J :=
  by
  refine' ⟨fun hIJ n a b ha hb hab => _, fun hIJ => _⟩
  · have hab' : a - b ∈ I := I.sub_mem ha hb
    rw [← add_sub_cancel'_right b a, hI.dpow_add n hb hab', Finset.range_succ,
      Finset.sum_insert Finset.not_mem_range_self, tsub_self, hI.dpow_zero hab', mul_one,
      add_sub_cancel']
    apply Ideal.sum_mem
    intro i hi
    apply SemilatticeInf.inf_le_left J I
    exact
      (J ⊓ I).smul_mem _
        (hIJ.dpow_mem_ideal (n - i) (ne_of_gt (Nat.sub_pos_of_lt (finset.mem_range.mp hi))) _
          ⟨hab, hab'⟩)
  · refine' ⟨SemilatticeInf.inf_le_right J I, fun n hn a ha => ⟨_, hI.dpow_mem hn ha.right⟩⟩
    rw [← sub_zero (hI.dpow n a), ← hI.dpow_eval_zero hn]
    exact hIJ n a 0 ha.right I.zero_mem (J.sub_mem ha.left J.zero_mem)
#align divided_powers.is_sub_pd_ideal_inf_iff DividedPowers.isSubPdIdeal_inf_iff

/-- Lemma 3.6 of [BO] (Antoine) -/
theorem span_isSubPdIdeal_iff (S : Set A) (hS : S ⊆ I) :
    IsSubPdIdeal hI (Ideal.span S) ↔ ∀ (n : ℕ) (hn : n ≠ 0), ∀ s ∈ S, hI.dpow n s ∈ Ideal.span S :=
  by
  constructor
  · -- trivial direction
    intro hhI h hn s hs
    apply hhI.dpow_mem_ideal h hn s (Ideal.subset_span hs)
  · -- interesting direction,
    intro hhI
    have hSI := ideal.span_le.mpr hS
    apply is_sub_pd_ideal.mk hSI
    intro n hn z hz; revert n
    refine' Submodule.span_induction' _ _ _ _ hz
    ·-- case of elements of S
      intro s hs n hn;
      exact hhI n hn s hs
    ·-- case of 0
      intro n hn;
      rw [hI.dpow_eval_zero hn]; apply Ideal.zero_mem _
    · -- case of sum
      rintro x hxI y hyI hx hy n hn
      rw [hI.dpow_add n (hSI hxI) (hSI hyI)]
      apply Submodule.sum_mem (Ideal.span S)
      intro m hm
      by_cases hm0 : m = 0
      · rw [hm0]
        exact Ideal.mul_mem_left (Ideal.span S) _ (hy n hn)
      · exact Ideal.mul_mem_right _ (Ideal.span S) (hx m hm0)
    · -- case : product,
      intro a x hxI hx n hn
      simp only [Algebra.id.smul_eq_mul]
      rw [hI.dpow_smul n (hSI hxI)]
      exact Ideal.mul_mem_left (Ideal.span S) (a ^ n) (hx n hn)
#align divided_powers.span_is_sub_pd_ideal_iff DividedPowers.span_isSubPdIdeal_iff

theorem generated_dpow_is_sub_ideal {S : Set A} (hS : S ⊆ I) :
    Ideal.span {y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x} ≤ I :=
  by
  rw [Ideal.span_le]
  rintro y ⟨n, hn, x, hx, hxy⟩
  rw [hxy]
  exact hI.dpow_mem hn (hS hx)
#align divided_powers.generated_dpow_is_sub_ideal DividedPowers.generated_dpow_is_sub_ideal

theorem isSubPdIdeal_sup {J K : Ideal A} (hJ : IsSubPdIdeal hI J) (hK : IsSubPdIdeal hI K) :
    IsSubPdIdeal hI (J ⊔ K) :=
  by
  rw [← J.span_eq, ← K.span_eq, ← Ideal.span_union, span_is_sub_pd_ideal_iff]
  · intro n hn a ha
    cases' ha with ha ha
    apply Ideal.span_mono (Set.subset_union_left ↑J ↑K)
    rw [J.span_eq]; exact hJ.2 n hn a ha
    apply Ideal.span_mono (Set.subset_union_right ↑J ↑K)
    rw [K.span_eq]; exact hK.2 n hn a ha
  rw [Set.union_subset_iff]; exact ⟨hJ.1, hK.1⟩
#align divided_powers.is_sub_pd_ideal_sup DividedPowers.isSubPdIdeal_sup

theorem Ideal.iSup_eq_span {ι : Type _} (p : ι → Ideal A) : (⨆ i, p i) = Ideal.span (⋃ i, ↑(p i)) :=
  Submodule.iSup_eq_span p
#align divided_powers.ideal.supr_eq_span DividedPowers.Ideal.iSup_eq_span

theorem isSubPdIdeal_iSup {ι : Type _} {J : ι → Ideal A} (hJ : ∀ i, IsSubPdIdeal hI (J i)) :
    IsSubPdIdeal hI (iSup J) := by
  rw [ideal.supr_eq_span]
  rw [span_is_sub_pd_ideal_iff]
  · rintro n hn a
    rw [Set.mem_iUnion]
    rintro ⟨i, ha⟩
    apply Ideal.span_mono (Set.subset_iUnion _ i)
    rw [Ideal.span_eq]; exact (hJ i).2 n hn a ha
  · rw [Set.iUnion_subset_iff]
    intro i; exact (hJ i).1
#align divided_powers.is_sub_pd_ideal_supr DividedPowers.isSubPdIdeal_iSup

theorem isSubPdIdeal_map {B : Type _} [CommRing B] {J : Ideal B} (hJ : DividedPowers J)
    {f : A →+* B} (hf : IsPdMorphism hI hJ f) (K : Ideal A) (hK : IsSubPdIdeal hI K) :
    IsSubPdIdeal hJ (Ideal.map f K) := by
  simp only [Ideal.map]
  rw [span_is_sub_pd_ideal_iff]
  rintro n hn y ⟨x, hx, rfl⟩
  rw [hf.2 n x (hK.1 hx)]
  apply Ideal.mem_map_of_mem
  exact hK.2 n hn x hx
  rintro y ⟨x, hx, rfl⟩
  exact hf.1 (Ideal.mem_map_of_mem f (hK.1 hx))
#align divided_powers.is_sub_pd_ideal_map DividedPowers.isSubPdIdeal_map

end IsSubPdIdeal

/-- A `sub-pd-ideal` of `I` is a sub-ideal `J` of `I` such that for all `n ∈ ℕ ≥ 0` and all
  `j ∈ J`, `hI.dpow n j ∈ J`. -/
@[ext]
structure SubPdIdeal {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I) where
  carrier : Ideal A
  is_sub_ideal : carrier ≤ I
  dpow_mem_ideal : ∀ (n : ℕ) (hn : n ≠ 0), ∀ j ∈ carrier, hI.dpow n j ∈ carrier
#align divided_powers.sub_pd_ideal DividedPowers.SubPdIdeal

namespace SubPdIdeal

variable {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)

def mk' (J : Ideal A) (hJ : IsSubPdIdeal hI J) : SubPdIdeal hI :=
  ⟨J, hJ.1, hJ.2⟩
#align divided_powers.sub_pd_ideal.mk' DividedPowers.SubPdIdeal.mk'

instance : SetLike (SubPdIdeal hI) A where
  coe s := s.carrier
  coe_injective' p q h := by rw [SetLike.coe_set_eq] at h  <;> cases p <;> cases q <;> congr

instance : Coe (SubPdIdeal hI) (Ideal A) :=
  ⟨fun J => J.carrier⟩

theorem coe_def (J : SubPdIdeal hI) : (J : Ideal A) = J.carrier :=
  rfl
#align divided_powers.sub_pd_ideal.coe_def DividedPowers.SubPdIdeal.coe_def

@[simp]
theorem mem_carrier {s : SubPdIdeal hI} {x : A} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align divided_powers.sub_pd_ideal.mem_carrier DividedPowers.SubPdIdeal.mem_carrier

def isSubPdIdeal (J : SubPdIdeal hI) : IsSubPdIdeal hI ↑J :=
  ⟨J.is_sub_ideal, J.dpow_mem_ideal⟩
#align divided_powers.sub_pd_ideal.is_sub_pd_ideal DividedPowers.SubPdIdeal.isSubPdIdeal

/-- If J is an ideal of A, then J ⬝ I is a sub-pd-ideal of I. (Berthelot, 1.6.1 (i)) -/
def prod (J : Ideal A) : SubPdIdeal hI
    where
  carrier := I • J
  is_sub_ideal := Ideal.mul_le_right
  dpow_mem_ideal n hn x hx := by
    revert n
    apply Submodule.smul_induction_on' hx
    · -- mul
      intro a ha b hb n hn
      rw [Algebra.id.smul_eq_mul, mul_comm a b, hI.dpow_smul n ha, mul_comm]
      exact Submodule.mul_mem_mul (hI.dpow_mem hn ha) (J.pow_mem_of_mem hb n (zero_lt_iff.mpr hn))
    · -- add
      intro x hx y hy hx' hy' n hn
      rw [hI.dpow_add n (Ideal.mul_le_right hx) (Ideal.mul_le_right hy)]
      apply Submodule.sum_mem (I • J)
      intro k hk
      by_cases hk0 : k = 0
      · rw [hk0]; apply Ideal.mul_mem_left (I • J); exact hy' _ hn
      · apply Ideal.mul_mem_right _ (I • J); exact hx' k hk0
#align divided_powers.sub_pd_ideal.prod DividedPowers.SubPdIdeal.prod

section CompleteLattice

instance : Coe (SubPdIdeal hI) { J : Ideal A // J ≤ I } :=
  ⟨fun J => ⟨J.carrier, J.is_sub_ideal⟩⟩

instance : LE (SubPdIdeal hI) :=
  ⟨fun J J' => J.carrier ≤ J'.carrier⟩

theorem le_iff {J J' : SubPdIdeal hI} : J ≤ J' ↔ J.carrier ≤ J'.carrier :=
  Iff.rfl
#align divided_powers.sub_pd_ideal.le_iff DividedPowers.SubPdIdeal.le_iff

instance : LT (SubPdIdeal hI) :=
  ⟨fun J J' => J.carrier < J'.carrier⟩

theorem lt_iff {J J' : SubPdIdeal hI} : J < J' ↔ J.carrier < J'.carrier :=
  Iff.rfl
#align divided_powers.sub_pd_ideal.lt_iff DividedPowers.SubPdIdeal.lt_iff

/-- I is a sub-pd-ideal ot itself. -/
instance : Top (SubPdIdeal hI) :=
  ⟨{  carrier := I
      is_sub_ideal := le_refl _
      dpow_mem_ideal := fun n hn x hx => hI.dpow_mem hn hx }⟩

instance inhabited : Inhabited hI.SubPdIdeal :=
  ⟨⊤⟩
#align divided_powers.sub_pd_ideal.inhabited DividedPowers.SubPdIdeal.inhabited

/-- (0) is a sub-pd-ideal ot the pd-ideal I. -/
instance : Bot (SubPdIdeal hI) :=
  ⟨{  carrier := ⊥
      is_sub_ideal := bot_le
      dpow_mem_ideal := fun n hn x hx => by
        rw [ideal.mem_bot.mp hx, hI.dpow_eval_zero hn, Ideal.mem_bot] }⟩

--Section 1.8 of [B]
-- The intersection of two sub-PD ideals is a sub-PD ideal.
instance : Inf (SubPdIdeal hI) :=
  ⟨fun J J' =>
    { carrier := J.carrier ⊓ J'.carrier
      is_sub_ideal := fun x hx => J.is_sub_ideal hx.1
      dpow_mem_ideal := fun n hn x hx =>
        ⟨J.dpow_mem_ideal n hn x hx.1, J'.dpow_mem_ideal n hn x hx.2⟩ }⟩

theorem inf_carrier_def (J J' : SubPdIdeal hI) : (J ⊓ J').carrier = J.carrier ⊓ J'.carrier :=
  rfl
#align divided_powers.sub_pd_ideal.inf_carrier_def DividedPowers.SubPdIdeal.inf_carrier_def

instance : InfSet (SubPdIdeal hI) :=
  ⟨fun S =>
    { carrier := ⨅ s ∈ Insert.insert ⊤ S, (s : hI.SubPdIdeal).carrier
      is_sub_ideal := fun x hx => by
        simp only [Ideal.mem_iInf] at hx 
        exact hx ⊤ (Set.mem_insert ⊤ S)
      dpow_mem_ideal := fun n hn x hx =>
        by
        simp only [Ideal.mem_iInf] at hx ⊢
        intro s hs
        refine' (s : hI.sub_pd_ideal).dpow_mem_ideal n hn x (hx s hs) }⟩

theorem sInf_carrier_def (S : Set (SubPdIdeal hI)) :
    (sInf S).carrier = ⨅ s ∈ Insert.insert ⊤ S, (s : hI.SubPdIdeal).carrier :=
  rfl
#align divided_powers.sub_pd_ideal.Inf_carrier_def DividedPowers.SubPdIdeal.sInf_carrier_def

instance : Sup (SubPdIdeal hI) :=
  ⟨fun J J' =>
    SubPdIdeal.mk' hI ((J : Ideal A) ⊔ J') <|
      by
      have hJJ' : (J : Ideal A) ⊔ (J' : Ideal A) = Ideal.span (J ∪ J') := by
        simp only [Ideal.span_union, coe_coe, Ideal.span_eq]
      rw [hJJ',
        span_is_sub_pd_ideal_iff hI (J ∪ J') (Set.union_subset J.is_sub_ideal J'.is_sub_ideal)]
      rintro n hn x (hx | hx)
      · exact Ideal.subset_span (Set.mem_union_left _ (J.dpow_mem_ideal n hn x hx))
      · exact Ideal.subset_span (Set.mem_union_right _ (J'.dpow_mem_ideal n hn x hx))⟩

theorem sup_carrier_def (J J' : SubPdIdeal hI) : (J ⊔ J').carrier = J ⊔ J' :=
  rfl
#align divided_powers.sub_pd_ideal.sup_carrier_def DividedPowers.SubPdIdeal.sup_carrier_def

instance : SupSet (SubPdIdeal hI) :=
  ⟨fun S =>
    SubPdIdeal.mk' hI (sSup ((coe : SubPdIdeal hI → Ideal A) '' S)) <|
      by
      have h : (⋃ (i : Ideal A) (hi : i ∈ coe '' S), ↑i) ⊆ (I : Set A) :=
        by
        rintro a ⟨-, ⟨J, rfl⟩, haJ⟩
        rw [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at haJ 
        obtain ⟨J', hJ'⟩ := (Set.mem_image _ _ _).mp haJ.1
        rw [← hJ'.2, coe_def] at haJ 
        exact J'.is_sub_ideal haJ.2
      rw [sSup_eq_iSup, Submodule.iSup_eq_span', Ideal.submodule_span_eq,
        span_is_sub_pd_ideal_iff hI _ h]
      rintro n hn x ⟨T, hT, hTx⟩
      obtain ⟨J, hJ⟩ := hT
      rw [← hJ] at hTx 
      obtain ⟨J', ⟨⟨hJ', rfl⟩, h'⟩⟩ := hTx
      apply Ideal.subset_span
      apply Set.mem_biUnion hJ'
      obtain ⟨K, hKS, rfl⟩ := hJ'
      exact K.dpow_mem_ideal n hn x h'⟩

theorem sSup_carrier_def (S : Set (SubPdIdeal hI)) :
    (sSup S).carrier = sSup ((coe : SubPdIdeal hI → Ideal A) '' S) :=
  rfl
#align divided_powers.sub_pd_ideal.Sup_carrier_def DividedPowers.SubPdIdeal.sSup_carrier_def

instance : CompleteLattice (SubPdIdeal hI) :=
  by
  refine'
    Function.Injective.completeLattice (fun J : sub_pd_ideal hI => (J : { J : Ideal A // J ≤ I }))
      (fun J J' h => (ext_iff _ _).mpr (subtype.ext_iff.mp h))
      (fun J J' => by rw [Subideal.sup_def] <;> rfl) (fun J J' => by rw [Subideal.inf_def] <;> rfl)
      _ _ (by rw [← Subideal.top_def] <;> rfl) (by rw [← Subideal.bot_def] <;> rfl)
  · intro S
    conv_rhs => rw [iSup]
    rw [Subideal.sSup_def, Subtype.ext_iff, ← coe_coe, coe_def, Sup_carrier_def, coe_mk, sSup_image,
      sSup_image, iSup_range]
    have :
      ∀ J : hI.sub_pd_ideal,
        ((⨆ H : J ∈ S, (J : { B : Ideal A // B ≤ I }) : { B : Ideal A // B ≤ I }) : Ideal A) =
          ⨆ H : J ∈ S, (J : Ideal A) :=
      by
      intro J
      by_cases hJ : J ∈ S
      · rw [ciSup_pos hJ, ciSup_pos hJ]; rfl
      · simp only [hJ, iSup_false, coe_eq_bot_iff, bot_le]
    simp_rw [this]
    ext a
    refine' ⟨fun ha => ⟨ha, _⟩, fun ha => ha.1⟩
    apply (Submodule.mem_iSup _).mp ha I
    intro J
    by_cases hJ : J ∈ S
    · rw [ciSup_pos hJ]; exact J.is_sub_ideal
    · simp only [hJ, iSup_false, bot_le]
  · intro S
    conv_rhs => rw [iInf]
    rw [Subideal.sInf_def, Subtype.ext_iff, ← coe_coe, coe_def, Inf_carrier_def, coe_mk, sInf_image,
      iInf_range, iInf_inf, iInf_insert, inf_iInf]
    apply iInf_congr
    intro J
    by_cases hJ : J ∈ S
    · rw [ciInf_pos hJ, ciInf_pos hJ, inf_comm]; rfl
    · simp only [hJ, iInf_false, inf_top_eq, ← Subideal.top_def, coe_mk, inf_idem]; rfl

end CompleteLattice

section Generated

/-- The sub-pd-ideal of I generated by a family of elements of A. -/
def generated (S : Set A) : SubPdIdeal hI :=
  sInf {J : SubPdIdeal hI | S ⊆ J.carrier}
#align divided_powers.sub_pd_ideal.generated DividedPowers.SubPdIdeal.generated

/-- The sub-pd-ideal of I generated by the family `hI.dpow n x`, where `n ≠ 0` and `x ∈ S`. -/
def generatedDpow {S : Set A} (hS : S ⊆ I) : SubPdIdeal hI
    where
  carrier := Ideal.span {y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x}
  is_sub_ideal := generated_dpow_is_sub_ideal hI hS
  dpow_mem_ideal n hn z hz :=
    by
    have hSI := generated_dpow_is_sub_ideal hI hS
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
      rw [hI.dpow_add n (hSI hx) (hSI hy)]
      apply Submodule.sum_mem (Ideal.span _)
      intro m hm
      by_cases hm0 : m = 0
      · rw [hm0]; exact Ideal.mul_mem_left (Ideal.span _) _ (hy_pow n hn)
      · exact Ideal.mul_mem_right _ (Ideal.span _) (hx_pow m hm0)
    · intro a x hx hx_pow n hn
      rw [smul_eq_mul, hI.dpow_smul n (hSI hx)]
      exact Ideal.mul_mem_left (Ideal.span _) (a ^ n) (hx_pow n hn)
#align divided_powers.sub_pd_ideal.generated_dpow DividedPowers.SubPdIdeal.generatedDpow

theorem generatedDpow_carrier {S : Set A} (hS : S ⊆ I) :
    (generatedDpow hI hS).carrier =
      Ideal.span {y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x} :=
  rfl
#align divided_powers.sub_pd_ideal.generated_dpow_carrier DividedPowers.SubPdIdeal.generatedDpow_carrier

theorem le_generatedDpow {S : Set A} (hS : S ⊆ I) : S ⊆ (generatedDpow hI hS).carrier := fun x hx =>
  Ideal.subset_span ⟨1, one_ne_zero, x, hx, by rw [hI.dpow_one (hS hx)]⟩
#align divided_powers.sub_pd_ideal.le_generated_dpow DividedPowers.SubPdIdeal.le_generatedDpow

theorem generated_dpow_le (S : Set A) (J : SubPdIdeal hI) (hSJ : S ⊆ J.carrier) :
    Ideal.span {y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x} ≤ J.carrier :=
  by
  rw [Ideal.span_le]
  rintro y ⟨n, hn, x, hx, hxy⟩
  rw [hxy]
  exact J.dpow_mem_ideal n hn x (hSJ hx)
#align divided_powers.sub_pd_ideal.generated_dpow_le DividedPowers.SubPdIdeal.generated_dpow_le

theorem generated_carrier_eq {S : Set A} (hS : S ⊆ I) :
    (generated hI S).carrier =
      Ideal.span {y : A | ∃ (n : ℕ) (hn : n ≠ 0) (x : A) (hx : x ∈ S), y = hI.dpow n x} :=
  by
  simp only [generated, Inf_carrier_def]
  apply le_antisymm
  · have h : generated_dpow hI hS ∈ insert ⊤ {J : hI.sub_pd_ideal | S ⊆ ↑J.carrier} :=
      by
      apply Set.mem_insert_of_mem
      simp only [Set.mem_setOf_eq, generated_dpow_carrier]
      exact le_generated_dpow hI hS
    refine' sInf_le_of_le ⟨generated_dpow hI hS, _⟩ (le_refl _)
    simp only [h, ciInf_pos]
    rfl
  · rw [le_iInf₂_iff]
    rintro J hJ
    refine' generated_dpow_le hI S J _
    cases' set.mem_insert_iff.mp hJ with hJI hJS
    · rw [hJI]; exact hS
    · exact hJS
#align divided_powers.sub_pd_ideal.generated_carrier_eq DividedPowers.SubPdIdeal.generated_carrier_eq

end Generated

end SubPdIdeal

section Ker

variable {A : Type _} {B : Type _} [CommRing A] [CommRing B] {I : Ideal A} (hI : DividedPowers I)
  {J : Ideal B} (hJ : DividedPowers J)

theorem isSubPdIdeal_ker {f : A →+* B} (hf : IsPdMorphism hI hJ f) :
    IsSubPdIdeal hI (RingHom.ker f ⊓ I) :=
  by
  rw [is_sub_pd_ideal_inf_iff]
  simp only [is_pd_morphism] at hf 
  intro n a b ha hb
  simp only [RingHom.sub_mem_ker_iff]
  rw [← hf.2 n a ha, ← hf.2 n b hb]
  exact congr_arg _
#align divided_powers.is_sub_pd_ideal_ker DividedPowers.isSubPdIdeal_ker

def PdMorphism.ker (f : PdMorphism hI hJ) : SubPdIdeal hI
    where
  carrier := RingHom.ker f.toRingHom ⊓ I
  is_sub_ideal := inf_le_right
  dpow_mem_ideal n hn a :=
    by
    simp only [Ideal.mem_inf, and_imp, RingHom.mem_ker]
    intro ha ha'
    rw [← f.is_pd_morphism.2 n a ha', ha]
    exact ⟨dpow_eval_zero hJ hn, hI.dpow_mem hn ha'⟩
#align divided_powers.pd_morphism.ker DividedPowers.PdMorphism.ker

end Ker

section Equalizer

variable {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)

/- TODO : The set of elements where two divided
powers coincide is the largest ideal which is a sub-pd-ideal in both -/
def pdEqualizer {A : Type _} [CommRing A] {I : Ideal A} (hI hI' : DividedPowers I) : Ideal A
    where
  carrier := {a ∈ I | ∀ n : ℕ, hI.dpow n a = hI'.dpow n a}
  add_mem' a b ha hb :=
    by
    simp only [Set.mem_sep_iff, SetLike.mem_coe] at ha hb ⊢
    apply And.intro (Ideal.add_mem I ha.1 hb.1)
    intro n
    rw [hI.dpow_add n ha.1 hb.1, hI'.dpow_add n ha.1 hb.1]
    apply Finset.sum_congr rfl
    intro k hk
    exact congr_arg₂ (· * ·) (ha.2 k) (hb.2 (n - k))
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
#align divided_powers.pd_equalizer DividedPowers.pdEqualizer

theorem mem_pdEqualizer_iff {A : Type _} [CommRing A] {I : Ideal A} (hI hI' : DividedPowers I)
    {x : A} : x ∈ pdEqualizer hI hI' ↔ x ∈ I ∧ ∀ n : ℕ, hI.dpow n x = hI'.dpow n x := by
  simp only [pd_equalizer, Submodule.mem_mk, Set.mem_sep_iff, SetLike.mem_coe]
#align divided_powers.mem_pd_equalizer_iff DividedPowers.mem_pdEqualizer_iff

theorem pdEqualizer_is_pd_ideal_left {A : Type _} [CommRing A] {I : Ideal A}
    (hI hI' : DividedPowers I) : DividedPowers.IsSubPdIdeal hI (pdEqualizer hI hI') :=
  by
  apply is_sub_pd_ideal.mk
  · intro x hx
    rw [mem_pd_equalizer_iff] at hx 
    exact hx.1
  · intro n hn x hx
    rw [mem_pd_equalizer_iff] at hx ⊢
    constructor
    apply hI.dpow_mem hn hx.1
    intro m
    rw [hI.dpow_comp m hn hx.1, hx.2, hx.2, hI'.dpow_comp m hn hx.1]
#align divided_powers.pd_equalizer_is_pd_ideal_left DividedPowers.pdEqualizer_is_pd_ideal_left

theorem pdEqualizer_is_pd_ideal_right {A : Type _} [CommRing A] {I : Ideal A}
    (hI hI' : DividedPowers I) : DividedPowers.IsSubPdIdeal hI' (pdEqualizer hI hI') :=
  by
  apply is_sub_pd_ideal.mk
  · intro x hx
    rw [mem_pd_equalizer_iff] at hx 
    exact hx.1
  · intro n hn x hx
    rw [mem_pd_equalizer_iff] at hx ⊢
    constructor
    apply hI'.dpow_mem hn hx.1
    intro m
    rw [← hx.2, hI.dpow_comp m hn hx.1, hx.2, hx.2, hI'.dpow_comp m hn hx.1]
#align divided_powers.pd_equalizer_is_pd_ideal_right DividedPowers.pdEqualizer_is_pd_ideal_right

/-- If there is a pd-structure on I(A/J) such that the quotient map is 
   a pd-morphism, then J ⊓ I is a sub-pd-ideal of I -/
def interQuot (J : Ideal A) (hJ : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (φ : PdMorphism hI hJ) (hφ : φ.toRingHom = Ideal.Quotient.mk J) : SubPdIdeal hI
    where
  carrier := J ⊓ I
  is_sub_ideal := Set.inter_subset_right J I
  dpow_mem_ideal := fun n hn a ⟨haJ, haI⟩ =>
    by
    refine' ⟨_, hI.dpow_mem hn haI⟩
    rw [SetLike.mem_coe, ← Ideal.Quotient.eq_zero_iff_mem, ← hφ, ← φ.dpow_comp n a haI]
    suffices ha0 : φ.to_ring_hom a = 0
    · rw [ha0]
      exact hJ.dpow_eval_zero hn
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact haJ
#align divided_powers.inter_quot DividedPowers.interQuot

theorem le_equalizer_of_pd_morphism {A : Type _} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type _} [CommRing B] (f : A →+* B) {K : Ideal B} (hI_le_K : Ideal.map f I ≤ K)
    (hK hK' : DividedPowers K) (hIK : IsPdMorphism hI hK f) (hIK' : IsPdMorphism hI hK' f) :
    Ideal.map f I ≤ pdEqualizer hK hK' := by
  rw [Ideal.map]; rw [Ideal.span_le]
  rintro b ⟨a, ha, rfl⟩
  simp only [SetLike.mem_coe] at ha ⊢
  rw [mem_pd_equalizer_iff]
  constructor
  apply hI_le_K; exact Ideal.mem_map_of_mem f ha
  simp only [is_pd_morphism, Ideal.map_id, RingHom.id_apply] at hIK hIK' 
  intro n
  rw [hIK.2 n a ha, hIK'.2 n a ha]
#align divided_powers.le_equalizer_of_pd_morphism DividedPowers.le_equalizer_of_pd_morphism

end Equalizer

section Quotient

/- Divided power structure on a quotient ring in two sorts:
* the case of a surjective ring_hom 
* specific case for ideal.quotient.mk   -/
namespace Quotient

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
#align divided_powers.quotient.of_surjective.dpow DividedPowers.Quotient.OfSurjective.dpow

variable (hIf : IsSubPdIdeal hI (f.ker ⊓ I))

variable {f}

/-- Divided powers on the quotient are compatible with quotient map -/
theorem dpow_apply' {n : ℕ} {a : A} (ha : a ∈ I) : dpow hI f n (f a) = f (hI.dpow n a) := by
  classical
  simp only [dpow, Function.extend_def]
  suffices : _
  rw [dif_pos this]
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]
  rw [is_sub_pd_ideal_inf_iff] at hIf 
  apply hIf n _ a _ ha
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  rw [this.some_spec]
  simp only [Submodule.coe_mem]
  · use ⟨a, ha⟩; simp only [Submodule.coe_mk]
#align divided_powers.quotient.of_surjective.dpow_apply' DividedPowers.Quotient.OfSurjective.dpow_apply'

/--
When `f.ker ⊓ I` is a `sub_pd_ideal` of `I`, the dpow map for the ideal `I.map f` of the target -/
noncomputable def dividedPowers : DividedPowers (I.map f)
    where
  dpow := dpow hI f
  dpow_null n x hx' := by
    classical
    simp only [dpow, Function.extend_def]
    rw [dif_neg]
    simp only [Pi.zero_apply]
    intro h
    obtain ⟨⟨a, ha⟩, rfl⟩ := h
    apply hx'
    exact Ideal.apply_coe_mem_map f I ⟨a, ha⟩
  dpow_zero x hx :=
    by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [dpow_apply' hI hf hIf ha, hI.dpow_zero ha, map_one]
  dpow_one x hx :=
    by
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [← hax, dpow_apply' hI hf hIf ha, hI.dpow_one ha]
  dpow_mem n hn x hx :=
    by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hf hIf ha]
    apply Ideal.mem_map_of_mem _ (hI.dpow_mem hn ha)
  dpow_add n x y hx hy :=
    by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hy
    rw [← map_add, dpow_apply' hI hf hIf (I.add_mem ha hb), hI.dpow_add n ha hb, map_sum,
      Finset.sum_congr rfl]
    · intro k hk
      rw [dpow_apply' hI hf hIf ha, dpow_apply' hI hf hIf hb, ← map_mul]
  dpow_smul n x y hy := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hy
    rw [dpow_apply' hI hf hIf hb, ← map_mul, ← map_pow,
      dpow_apply' hI hf hIf (Ideal.mul_mem_left I a hb), hI.dpow_smul n hb, map_mul]
  dpow_mul m n x hx :=
    by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hf hIf ha]
    rw [← map_mul, hI.dpow_mul m n ha, map_mul, map_natCast]
  dpow_comp m n hn x hx :=
    by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    simp only [dpow_apply' hI hf hIf, ha, hI.dpow_mem hn ha]
    rw [hI.dpow_comp m hn ha, map_mul, map_natCast]
#align divided_powers.quotient.of_surjective.divided_powers DividedPowers.Quotient.OfSurjective.dividedPowers

theorem dpow_def {n : ℕ} {x : B} : (dividedPowers hI hf hIf).dpow n x = dpow hI f n x :=
  rfl
#align divided_powers.quotient.of_surjective.dpow_def DividedPowers.Quotient.OfSurjective.dpow_def

theorem dpow_apply {n : ℕ} {a : A} (ha : a ∈ I) :
    (dividedPowers hI hf hIf).dpow n (f a) = f (hI.dpow n a) := by
  rw [dpow_def, dpow_apply' hI hf hIf ha]
#align divided_powers.quotient.of_surjective.dpow_apply DividedPowers.Quotient.OfSurjective.dpow_apply

theorem isPdMorphism : IsPdMorphism hI (dividedPowers hI hf hIf) f :=
  by
  constructor
  exact le_refl (Ideal.map f I)
  intro n a ha; rw [dpow_apply hI hf hIf ha]
#align divided_powers.quotient.of_surjective.is_pd_morphism DividedPowers.Quotient.OfSurjective.isPdMorphism

theorem unique (hquot : DividedPowers (I.map f)) (hm : DividedPowers.IsPdMorphism hI hquot f) :
    hquot = dividedPowers hI hf hIf :=
  eq_of_eq_on_ideal _ _ fun n x hx =>
    by
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp hx
    rw [hm.2 n a ha, dpow_apply hI hf hIf ha]
#align divided_powers.quotient.of_surjective.unique DividedPowers.Quotient.OfSurjective.unique

end OfSurjective

end OfSurjective

variable {J : Ideal A} (hIJ : IsSubPdIdeal hI (J ⊓ I))

/- Tagged as noncomputable because it makes use of function.extend, 
but under is_sub_pd_ideal hI (J ⊓ I), dpow_quot_eq proves that no choices are involved -/
/-- The definition of divided powers on A ⧸ J -/
noncomputable def dpow (J : Ideal A) : ℕ → A ⧸ J → A ⧸ J :=
  DividedPowers.Quotient.OfSurjective.dpow hI (Ideal.Quotient.mk J)
#align divided_powers.quotient.dpow DividedPowers.Quotient.dpow

--TODO: think about whether this should be a lemma
private theorem is_sub_pd_aux : IsSubPdIdeal hI ((Ideal.Quotient.mk J).ker ⊓ I) := by
  simpa [Ideal.mk_ker] using hIJ

-- We wish for a better API to denote I.map (ideal.quotient.mk J) as I ⧸ J
/-- When `I ⊓ J` is a `sub_pd_ideal` of `I`, the dpow map for the ideal `I(A⧸J)` of the quotient -/
noncomputable def dividedPowers : DividedPowers (I.map (Ideal.Quotient.mk J)) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers hI Ideal.Quotient.mk_surjective
    (is_sub_pd_aux hI hIJ)
#align divided_powers.quotient.divided_powers DividedPowers.Quotient.dividedPowers

/-- Divided powers on the quotient are compatible with quotient map -/
theorem dpow_apply {n : ℕ} {a : A} (ha : a ∈ I) :
    (dividedPowers hI hIJ).dpow n (Ideal.Quotient.mk J a) = (Ideal.Quotient.mk J) (hI.dpow n a) :=
  DividedPowers.Quotient.OfSurjective.dpow_apply hI Ideal.Quotient.mk_surjective
    (is_sub_pd_aux hI hIJ) ha
#align divided_powers.quotient.dpow_apply DividedPowers.Quotient.dpow_apply

theorem isPdMorphism : DividedPowers.IsPdMorphism hI (dividedPowers hI hIJ) (Ideal.Quotient.mk J) :=
  DividedPowers.Quotient.OfSurjective.isPdMorphism hI Ideal.Quotient.mk_surjective
    (is_sub_pd_aux hI hIJ)
#align divided_powers.quotient.is_pd_morphism DividedPowers.Quotient.isPdMorphism

theorem unique (hquot : DividedPowers (I.map (Ideal.Quotient.mk J)))
    (hm : DividedPowers.IsPdMorphism hI hquot (Ideal.Quotient.mk J)) :
    hquot = dividedPowers hI hIJ :=
  DividedPowers.Quotient.OfSurjective.unique hI Ideal.Quotient.mk_surjective (is_sub_pd_aux hI hIJ)
    hquot hm
#align divided_powers.quotient.unique DividedPowers.Quotient.unique

end Quotient

end Quotient

end DividedPowers

