import DividedPowers.DPAlgebra.Dpow

universe u v w

open DividedPowerAlgebra DividedPowers Ideal

namespace DividedPowers

-- I think we need to remove the condition `a ∈ I` from the definition of isDPMorphism
/-- Compatibility of a ring morphism with dp-structures -/
def isDPMorphism' {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  I.map f ≤ J ∧ ∀ (n : ℕ), ∀ a : A, hJ.dpow n (f a) = f (hI.dpow n a)

/- /-- Compatibility of a ring morphism with dp-structures -/
structure isDPMorphism' {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop where
  map_le : I.map f ≤ J
  map_mem : ∀ (n : ℕ), ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)
  map_not_mem : ∀ (n : ℕ), ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) -/


--Move these to "Extensions/Compatible" file
/-- B-0 Def 3.14 -/
def extends_to {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] (f : A →+* B) : Prop :=
  ∃ hI' : DividedPowers (I.map f), isDPMorphism' hI hI' f

-- Note (1) after 3.14
lemma extends_to_unique {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] (f : A →+* B) (hext : extends_to hI f) {hK : DividedPowers (I.map f)}
    (hmap : isDPMorphism' hI hK f) :
    hK = hext.choose := by
  obtain ⟨hI', hI'map⟩ := hext
  simp only [isDPMorphism', le_refl, true_and] at hmap hI'map
  ext n b
  sorry

-- Note (2) after 3.14
lemma extends_to_iff_exists_dpIdeal {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :
    extends_to hI f ↔  ∃ (J : Ideal B) (hJ : DividedPowers J), isDPMorphism' hI hJ f := by
  classical
  refine ⟨fun ⟨hJ, hmap⟩ ↦ ⟨I.map f, hJ, hmap⟩, fun ⟨J, hJ, hmap⟩ ↦  ?_⟩
  have hsub : isSubDPIdeal hJ (I.map f) := sorry -- use 3.6
  use hsub.dividedPowers
  rw [isDPMorphism'] at hmap ⊢
  refine ⟨le_refl _, ?_⟩
  intros n a
  rw [isSubDPIdeal.dividedPowers.dpow_eq]
  by_cases ha : a ∈ I
  · rw [← hmap.2 n a, if_pos (mem_map_of_mem _ ha)]
  · rw [if_neg, dpow_null _ ha, map_zero]
    sorry


-- Note (3) after 3.14: in general the extension does not exist.

-- B-O Prop. 3.15
lemma extends_to_of_principal {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    (hIp : Submodule.IsPrincipal I) {B : Type v} [CommRing B] (f : A →+* B) :
    extends_to hI f  := by
  sorry

-- B-O Prop. 3.16
lemma IsCompatibleWith_tfae {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) :
    List.TFAE  [∃ hI' : DividedPowers (I.map f),  isDPMorphism' hI hI' f ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hJ.dpow n b = hI'.dpow n b,
      ∃ hK : DividedPowers (I.map f + J),  isDPMorphism' hI hK f ∧ isDPMorphism' hJ hK (RingHom.id _),
      ∃ (K' : Ideal B) (hIJK : I.map f + J ≤ K') (hK' : DividedPowers K'),
      isDPMorphism' hI hK' f ∧ isDPMorphism' hJ hK' (RingHom.id _)] := by
  tfae_have 1 → 2
  · sorry
  tfae_have 2 → 3
  · rintro ⟨hK, hIK, hJK⟩
    use I.map f + J, le_refl _, hK
  tfae_have 3 → 1
  · rintro ⟨K, hIJK, hK, hIK, hJK⟩
    have hB : extends_to hI f := sorry
    obtain ⟨hI', hI'J⟩ := hB
    use hI', hI'J
    rintro n b ⟨hbJ, hbI⟩
    simp only [isDPMorphism', le_refl, true_and, map_id, RingHom.id_apply] at hIK hI'J hJK
    rw [ ← hJK.2 n b]
    rw [SetLike.mem_coe, map, ← submodule_span_eq] at hbI
    revert n
    apply Submodule.span_induction hbI
      (p := fun b ↦ ∀ n, hK.dpow n b = hI'.dpow n b)
    · rintro b ⟨a, haI, rfl⟩ n
      rw [hIK.2 n a, hI'J n a]
    · intro n
      by_cases hn : n = 0
      · rw [hn, dpow_zero _ (Submodule.zero_mem _), dpow_zero _ (Submodule.zero_mem _)]
      · rw [dpow_eval_zero _ hn, dpow_eval_zero _ hn]
    · intro x y hx hy n
      by_cases hxJ : x ∈ J
      · have hyJ : y ∈ J := sorry
        rw [dpow_add _ _ (hJK.1 hxJ) (hJK.1 hyJ)]
        sorry
      ·
        sorry --  rw [dpow_add]
      --simp? [dpow_zero]
    · intro c x hx n
      by_cases hxJ : x ∈ J
      · rw [dpow_smul' _ _ _ (hJK.1 hxJ), hx n]
        by_cases hxI' : x ∈ I.map f
        · rw [dpow_smul' _ _ _ hxI']
        · sorry
      · sorry

  tfae_finish

-- TODO: use (2) instead
-- Or use 3.6 to construct this.
/-- B-0 Def 3.17 (using condition 1 of Prop. 3.16) -/
def IsCompatibleWith {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  ∃ hI' : DividedPowers (I.map f),
    (∀ (n : ℕ) (a : A), hI'.dpow n (f a) = f (hI.dpow n a)) ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hJ.dpow n b = hI'.dpow n b


end DividedPowers
