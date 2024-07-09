import DividedPowers.DPAlgebra.Dpow

universe u v w

open DividedPowerAlgebra DividedPowers Ideal

namespace DividedPowers

-- I think we  need to remove the condition `a ∈ I` from the definition of isDPMorphism
/-- Compatibility of a ring morphism with dp-structures -/
def isDPMorphism' {A B : Type _} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  I.map f ≤ J ∧ ∀ n > 0, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)

--Move these to "Extensions/Compatible" file
/-- B-0 Def 3.14 -/
def extends_to {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] (f : A →+* B) : Prop :=
  ∃ hI' : DividedPowers (I.map f), isDPMorphism hI hI' f

lemma isDPMorphism.span_map_le {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) (K : Ideal B) (hK : DividedPowers K)
      (hIKf : isDPMorphism hI hK f) :
      Submodule.span B (f '' I) ≤ K := by
  apply le_trans _ hIKf.1
  rw [submodule_span_eq, map]

-- Note (1) after 3.14
lemma extends_to_unique {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] (f : A →+* B) (hext : extends_to hI f) {hK : DividedPowers (I.map f)}
    (hmap : isDPMorphism hI hK f) :
    hK = hext.choose := by
  set hI' := hext.choose with hI'_def
  let hI'map := hext.choose_spec
  rw [← hI'_def] at hI'map
  simp only [isDPMorphism, le_refl, true_and] at hmap hI'map
  ext n b
  by_cases hb : b ∈ I.map f
  · rw [map, ← submodule_span_eq] at hb
    revert n
    apply Submodule.span_induction' (p := fun b _ ↦  ∀ n, hK.dpow n b = hI'.dpow n b)
          _ _ _ _ hb
    · intro x hx n
      simp only [Set.mem_image, SetLike.mem_coe] at hx
      obtain ⟨a, haI, rfl⟩ := hx
      rw [hmap n a haI, hI'map n a haI]
    · intro n
      by_cases hn0 : n = 0
      · rw [hn0, hK.dpow_zero (Submodule.zero_mem (map f I)),
          hI'.dpow_zero (Submodule.zero_mem (map f I))]
      · rw [hK.dpow_eval_zero hn0, hI'.dpow_eval_zero hn0]
    · intros x hxmem y hymem hx hy n
      rw [submodule_span_eq, ← map] at hxmem hymem
      rw [hK.dpow_add _ hxmem hymem, hI'.dpow_add _ hxmem hymem]
      exact Finset.sum_congr rfl (fun nm _ ↦ by rw [hx nm.1, hy nm.2])
    · intro c x hxmem hx n
      rw [submodule_span_eq, ← map] at hxmem
      rw [dpow_smul' _ _ _ hxmem, dpow_smul' _ _ _ hxmem, hx n]
  · rw [dpow_null _ hb, dpow_null _ hb]

-- Note (2) after 3.14
lemma extends_to_iff_exists_dpIdeal {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) :
    extends_to hI f ↔ ∃ (J : Ideal B) (hJ : DividedPowers J), isDPMorphism hI hJ f := by
  classical
  refine ⟨fun ⟨hJ, hmap⟩ ↦ ⟨I.map f, hJ, hmap⟩, fun ⟨J, hJ, hmap⟩ ↦  ?_⟩
  have hsub : isSubDPIdeal hJ (I.map f) := by
    apply isSubDPIdeal_map _ _ hmap
  use hsub.dividedPowers
  rw [isDPMorphism] at hmap ⊢
  refine ⟨le_refl _, ?_⟩
  intros n a ha
  rw [isSubDPIdeal.dividedPowers.dpow_eq, if_pos (I.mem_map_of_mem f ha), hmap.2 n a ha]

-- Note (3) after 3.14: in general the extension does not exist.

lemma _root_.Submodule.map_isPrincipal {A : Type u} [CommRing A] {I : Ideal A}
    (hIp : Submodule.IsPrincipal I) {B : Type v} [CommRing B] (f : A →+* B) :
    Submodule.IsPrincipal (I.map f) := by
  obtain ⟨t, ht⟩ := hIp
  use f t
  simp only [ht, submodule_span_eq, map_span, Set.image_singleton]

lemma _root_.Ideal.map_span_singleton {A : Type u} [CommRing A] (a : A) {B : Type v} [CommRing B]
    (f : A →+* B) : (Ideal.span {a}).map f = Ideal.span {f a} := by
  simp only [map_span, Set.image_singleton]

-- B-O Prop. 3.15
lemma extends_to_of_principal {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    (hIp : Submodule.IsPrincipal I) {B : Type v} [CommRing B] (f : A →+* B) :
    extends_to hI f  := by
  classical
  obtain ⟨t, ht⟩ := hIp
  have htI : t ∈ I := ht ▸ Ideal.mem_span_singleton_self t
  have hIf : ∀ {x : B}, x ∈ I.map f ↔ ∃ c : B, c * (f t) = x:= by
    intro x
    rw [ht, submodule_span_eq, map_span_singleton, ← submodule_span_eq,
      Submodule.mem_span_singleton]
    simp_rw [smul_eq_mul]
  set hI' : DividedPowers (I.map f) := {
    dpow      := fun n b ↦ if hb : b ∈ I.map f then
      let c := (hIf.mp hb).choose
      c^n * f (hI.dpow n t)
      else 0
    dpow_null := fun hb ↦ by
      simp only [← hIf, smul_eq_mul, dite_eq_right_iff]
      exact fun hb' ↦ absurd hb' hb
    dpow_zero  := fun hb ↦ by
      simp only [dif_pos hb, smul_eq_mul, pow_zero, one_mul, dpow_zero _ htI, map_one]
    dpow_one  := fun hb ↦  by
      simp only [dif_pos hb, dpow_one _ htI, pow_one, (hIf.mp hb).choose_spec]
    dpow_mem  := fun hn hb ↦ by
      simp only [dif_pos hb]
      exact Submodule.smul_mem _ _ (mem_map_of_mem _ (hI.dpow_mem hn htI))
    dpow_add  := fun n b c hb hc ↦ by
      simp only [dif_pos (add_mem hb hc), dif_pos hb, dif_pos hc]
      simp_rw [mul_assoc, ← mul_assoc (f _), mul_comm (f _), mul_assoc, ← _root_.map_mul f,
        dpow_mul hI _ _ htI, _root_.map_mul]

      sorry
    dpow_smul := by
      intro n c x hx
      have hcx : c * x ∈ map f I := by simp only [← smul_eq_mul, Submodule.smul_mem _ _ hx]
      simp only [dif_pos hcx, dif_pos hx]
      by_cases hn : n = 0
      · simp only [hn, pow_zero, one_mul]
      · rw [hIf] at hx hcx
        set a := hx.choose with ha
        set ca := hcx.choose with hca
        rw [← mul_assoc, ← sub_eq_zero, ← sub_mul, ← mul_pow]
        obtain ⟨k, hk⟩ := dvd_iff_exists_eq_mul_left.mp (sub_dvd_pow_sub_pow ca (c * a) n)
        rw [hk, mul_assoc]
        apply mul_eq_zero_of_right
        have hnt : hI.dpow n t ∈ I := dpow_mem hI hn htI
        simp only [ht] at hnt
        rw [submodule_span_eq, ← submodule_span_eq, Submodule.mem_span_singleton] at hnt
        obtain ⟨ct, hct⟩ := hnt
        rw [← hct, smul_eq_mul, _root_.map_mul, mul_comm (f _), ← mul_assoc, sub_mul]
        apply mul_eq_zero_of_left
        rw [sub_eq_zero, hcx.choose_spec, mul_assoc, hx.choose_spec]
    dpow_mul  := fun _ _ _ hx ↦ by
      simp only [dif_pos hx]
      rw [mul_assoc, mul_comm _ (f _), ← mul_assoc (f _), ← _root_.map_mul, dpow_mul _ _ _ htI,
        _root_.map_mul, map_natCast]
      ring
    dpow_comp := by
      intro m n x hn hx
      have hnt : hI.dpow n t ∈ I := dpow_mem hI hn htI
      /- simp only [ht] at hnt
      rw [submodule_span_eq, ← submodule_span_eq, Submodule.mem_span_singleton] at hnt
      set cnt := hnt.choose with hcnt -/
      simp only [dif_pos hx]
      simp only [ht] at hx
      rw [submodule_span_eq, map_span_singleton, ← submodule_span_eq, Submodule.mem_span_singleton]
        at hx
      set cx := hx.choose with hcx
      have := hx.choose_spec
      simp_rw [← hcx]
      have h :  cx ^ n * f (hI.dpow n t) ∈ map f I := sorry
      rw [dif_pos h]
      simp only [ht] at h
      rw [submodule_span_eq, map_span_singleton, ← submodule_span_eq, Submodule.mem_span_singleton]
        at h
      set cxn := h.choose with hcxn_def
      set hcxn := h.choose_spec
      rw [← mul_assoc, mul_comm _ (cx^_)]
      rw [← map_natCast f, mul_assoc, ← _root_.map_mul]
      rw [← hI.dpow_comp _ hn htI]
      have hm : cx ^ (m * n) = (cx ^n)^m := sorry
      rw [hm]
      rw [← sub_eq_zero]

      have hcm : f (hI.dpow m (hI.dpow n t)) ∈ map f I := sorry
      simp only [ht] at hcm
      rw [submodule_span_eq, map_span_singleton, ← submodule_span_eq, Submodule.mem_span_singleton]
        at hcm
      set cxm := hcm.choose with hcxm_def
      set hcxm := hcm.choose_spec
      rw [← hcxm, ← hcxm_def]

      /- suffices f (cxn * hI.dpow m t) = f (cx^n * hI.dpow m (hI.dpow n t)) by
        sorry -/


      --rw [hI.dpow_smul]
      --have h := Submodule.smul_mem (I.map f) _ (mem_map_of_mem _ (hI.dpow_mem hn htI))
      --rw [dif_pos (Submodule.smul_mem (I.map f) _ (mem_map_of_mem _ (hI.dpow_mem hn htI)))]
      --simp only [smul_eq_mul]
     /-  rw [← smul_assoc]
      simp only [smul_eq_mul]
      rw [← map_natCast f]
      nth_rewrite 2 [mul_comm] -/
      --rw [hI.dpow_comp]
      sorry
       }
  use hI'
  rw [isDPMorphism]
  refine ⟨le_refl _, ?_⟩
  intro n a haI
  simp only [dif_pos (mem_map_of_mem _ haI)]
  set s := (hIf.mp (mem_map_of_mem _ haI)).choose with hs
  by_cases hn : n = 0
  · rw [hn, dpow_zero _ htI, dpow_zero _ haI, pow_zero, one_mul]
  · rw [ht, submodule_span_eq, ← submodule_span_eq, Submodule.mem_span_singleton] at haI
    obtain ⟨a, rfl⟩ := haI
    have hnt : ∃ (c : A), c • t = hI.dpow n  t := by
      rw [← Submodule.mem_span_singleton, ← ht]
      exact dpow_mem hI hn htI
    obtain ⟨c, hct⟩ := hnt
    rw [← sub_eq_zero, dpow_smul' _ _ _ htI, smul_eq_mul, _root_.map_mul, map_pow, ← sub_mul, ← hct,
      smul_eq_mul, _root_.map_mul, mul_comm (f c), ← mul_assoc]
    apply mul_eq_zero_of_left
    obtain ⟨k, hk⟩ := dvd_iff_exists_eq_mul_left.mp (sub_dvd_pow_sub_pow s (f a) n)
    rw [hk, mul_assoc]
    apply mul_eq_zero_of_right
    rw [sub_mul, sub_eq_zero, (hIf.mp (mem_map_of_mem _ haI)).choose_spec, ← _root_.map_mul]
    rfl

lemma isDPMorphism.isSubDPIdeal_map {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] (f : A →+* B) {K : Ideal B} (hK : DividedPowers K)
    (hIK : isDPMorphism hI hK f) :
    isSubDPIdeal hK (I.map f) := {
      isSubIdeal := hIK.1
      dpow_mem   := by
        have hsub : Submodule.span B (f '' I) ≤ K := by
          apply le_trans _ hIK.1
          rw [submodule_span_eq, map]
        intro n hn c hc
        rw [map, ← submodule_span_eq] at hc
        revert n
        apply Submodule.span_induction' (p := fun c _ ↦  ∀ n (_ : n ≠ 0), hK.dpow n c ∈ map f I)
          _ _ _ _ hc
        · intro x hxmem n hn
          simp only [Set.mem_image, SetLike.mem_coe] at hxmem
          obtain ⟨a, haI, rfl⟩ := hxmem
          rw [← hIK.map_dpow n a haI]
          exact mem_map_of_mem _ (hI.dpow_mem hn haI)
        · intro n hn
          rw [hK.dpow_eval_zero hn]
          exact Submodule.zero_mem (map f I)
        · intro x hxmem y hymem hx hy n hn
          suffices Submodule.span B (f '' I) ≤ K by
            rw [hK.dpow_add n (this hxmem) (this hymem)]
            apply Ideal.sum_mem
            intro nm hnm
            by_cases hnm1 : nm.1 = 0
            · have hnm2 : nm.2 ≠ 0 := by
                rw [Finset.mem_antidiagonal, hnm1, zero_add] at hnm
                rwa [hnm]
              exact (I.map f).mul_mem_left _ (hy _ hnm2)
            · exact (I.map f).mul_mem_right _ (hx _ hnm1)
          exact hsub
        · intro c x hxmem hx n hn
          suffices Submodule.span B (f '' I) ≤ K by
            rw [hK.dpow_smul' _ _ (this hxmem)]
            exact Submodule.smul_mem  _ _ (hx n hn)
          exact hsub }

-- B-O Prop. 3.16
lemma IsCompatibleWith_tfae {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) :
    List.TFAE  [∃ hI' : DividedPowers (I.map f),  isDPMorphism hI hI' f ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hJ.dpow n b = hI'.dpow n b,
      ∃ hK : DividedPowers (I.map f + J), isDPMorphism hI hK f ∧ isDPMorphism hJ hK (RingHom.id _),
      ∃ (K' : Ideal B) (hIJK : I.map f + J ≤ K') (hK' : DividedPowers K'),
      isDPMorphism hI hK' f ∧ isDPMorphism hJ hK' (RingHom.id _)] := by
  classical
  tfae_have 1 → 2
  · sorry
  tfae_have 2 → 3
  · rintro ⟨hK, hIK, hJK⟩
    use I.map f + J, le_refl _, hK
  tfae_have 3 → 1
  · rintro ⟨K, hIJK, hK, hIK, hJK⟩
    /- -- proof by MI
    have hB : extends_to hI f := sorry
    obtain ⟨hI', hI'J⟩ := hB
    use hI', hI'J
    rintro n b ⟨hbJ, hbI⟩
    simp only [isDPMorphism', le_refl, true_and, map_id, RingHom.id_apply] at hIK hI'J hJK
    have hsub : isSubDPIdeal hK (I.map f) := isDPMorphism.isSubDPIdeal_map hI f hK hIK
    set hK' : DividedPowers (map f I) := isSubDPIdeal.dividedPowers hK hsub
    have hKI' : hI' = hK' := by
      sorry --uniqueness theorem
    rw [hKI']
    rw [isSubDPIdeal.dividedPowers.dpow_eq_of_mem _ _ _ hbI]
    by_cases hn : n = 0
    · rw [hn, dpow_zero _ (hJK.1 hbJ), dpow_zero _ hbJ]
    · exact (hJK.2 _ (Nat.zero_lt_of_ne_zero hn) _ hbJ).symm -/
    have hsub : isSubDPIdeal hK (I.map f) := isDPMorphism.isSubDPIdeal_map hI f hK hIK
    set hK' : DividedPowers (map f I) := isSubDPIdeal.dividedPowers hK hsub
    use hK'
    constructor
    · simp only [isDPMorphism, le_refl, true_and]
      intro n a ha
      -- we need some API to use isSubDPIdeal.dividedPowers
      simp only [hK', isSubDPIdeal.dividedPowers]
      rw [if_pos (Ideal.mem_map_of_mem f ha), hIK.map_dpow n a ha]
    · rintro n b ⟨hb , hb'⟩
      simp only [SetLike.mem_coe] at hb hb'
      -- we need some API to use isSubDPIdeal.dividedPowers
      simp only [hK', isSubDPIdeal.dividedPowers]
      have := hJK.map_dpow n b hb
      simp only [RingHom.id_apply] at this
      rw [if_pos hb', show hJ.dpow n b = hK.dpow n b by
        simpa only [RingHom.id_apply] using hJK.map_dpow n b hb]
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
