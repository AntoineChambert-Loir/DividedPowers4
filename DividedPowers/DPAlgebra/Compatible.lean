import DividedPowers.DPAlgebra.Dpow

universe u v w

open DividedPowerAlgebra DividedPowers Ideal

namespace DividedPowers

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
    apply Submodule.span_induction' (p := fun b _ ↦  ∀ n, hK.dpow n b = hI'.dpow n b) _ _ _ _ hb
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
  use (isSubDPIdeal_map _ _ hmap).dividedPowers
  rw [isDPMorphism] at hmap ⊢
  refine ⟨le_refl _, ?_⟩
  intros n a ha
  rw [isSubDPIdeal.dividedPowers.dpow_eq, if_pos (I.mem_map_of_mem f ha), hmap.2 n a ha]

-- Note (3) after 3.14: in general the extension does not exist.

namespace IsPrincipal
-- In this section we proveB-O Prop. 3.15

open Function Ideal

lemma _root_.Submodule.map_isPrincipal {A : Type u} [CommRing A] {I : Ideal A}
    (hIp : Submodule.IsPrincipal I) {B : Type v} [CommRing B] (f : A →+* B) :
    Submodule.IsPrincipal (I.map f) := by
  obtain ⟨t, ht⟩ := hIp
  use f t, by simp only [ht, submodule_span_eq, map_span, Set.image_singleton]

lemma _root_.Ideal.map_span_singleton {A : Type u} [CommRing A] (a : A) {B : Type v} [CommRing B]
    (f : A →+* B) : (span {a}).map f = span {f a} := by
  simp only [map_span, Set.image_singleton]

lemma factorsThrough {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {t : A}
    (hIt : I = span {t}) {B : Type v} [CommRing B] (f : A →+* B) (n : ℕ) :
    Function.FactorsThrough (fun (c : B) ↦ c^n * f (hI.dpow n t)) (fun (c : B) ↦ c * f t) := by
  intro b c hbc
  simp only at hbc ⊢
  by_cases hn : n = 0
  · rw [hn, pow_zero, pow_zero]
  · have hnt : hI.dpow n t ∈ I := dpow_mem hI hn (hIt ▸ mem_span_singleton_self t)
    simp only [hIt, mem_span_singleton'] at hnt
    obtain ⟨cnt, hcnt⟩ := hnt
    rw [← sub_eq_zero, ← sub_mul, ← hcnt, _root_.map_mul, mul_comm (f cnt), ← mul_assoc]
    apply mul_eq_zero_of_left
    obtain ⟨k, hk⟩ := dvd_iff_exists_eq_mul_left.mp (sub_dvd_pow_sub_pow b c n)
    rw [hk, mul_assoc]
    apply mul_eq_zero_of_right
    rw [sub_mul, sub_eq_zero, hbc]

variable {A : Type u} [CommRing A] {I : Ideal A} {t : A} (hIt : I = span {t})
  {B : Type v} [CommRing B] {f : A →+* B} {x : B}

lemma _root_.Ideal.mem_map_span_singleton : x ∈ I.map f ↔ ∃ c : B, c * (f t) = x := by
  simp_rw [hIt, map_span_singleton, ← submodule_span_eq, Submodule.mem_span_singleton, smul_eq_mul]

lemma _root_.Ideal.not_mem_map_span_singleton : x ∉ I.map f ↔ ¬ ∃ c : B, c * (f t) = x := by
  rw [mem_map_span_singleton hIt]

variable (f)

/-- The extension of the divided power structure on the principal ideal `I` to `I.map f`. -/
noncomputable def extension (hIt : I = span {t}) (hI : DividedPowers I) :
    DividedPowers (I.map f) where
  dpow n := extend (fun (c : B) ↦ c * f t) (fun (c : B) ↦ c^n * f (hI.dpow n t)) 0
  dpow_null hx := by
    simp only [extend_apply' _ _ _ ((not_mem_map_span_singleton hIt).mp hx),
      Pi.zero_apply]
  dpow_zero hx := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    dsimp only
    rw [(factorsThrough hI hIt f 0).extend_apply, pow_zero, one_mul,
      hI.dpow_zero (hIt ▸ mem_span_singleton_self t), map_one]
  dpow_one hx := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    dsimp only
    rw [(factorsThrough hI hIt f 1).extend_apply, pow_one,
      hI.dpow_one (hIt ▸ mem_span_singleton_self t)]
  dpow_mem hn hx := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    simp only [(factorsThrough hI hIt f _).extend_apply]
    exact Submodule.smul_mem _ _ (mem_map_of_mem _
      (hI.dpow_mem hn (hIt ▸ mem_span_singleton_self t)))
  dpow_add n x y hx hy := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    obtain ⟨cy, rfl⟩ := (mem_map_span_singleton hIt).mp hy
    simp only [← add_mul, (factorsThrough hI hIt f n).extend_apply, (Commute.all cx cy).add_pow',
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    rintro ⟨r, s⟩ hrs
    simp only [(factorsThrough hI hIt f _).extend_apply]
    have : cx ^ r * f (hI.dpow r t) * (cy ^ s * f (hI.dpow s t)) =
        cx ^ r * cy ^ s * (f ((hI.dpow r t) * (hI.dpow s t))) := by
      rw [_root_.map_mul]
      ring
    rw [this, hI.dpow_mul _ _ (hIt ▸ mem_span_singleton_self t),
      Finset.mem_antidiagonal.mp hrs, _root_.map_mul, map_natCast]
    ring
  dpow_smul n a x hx := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    dsimp only
    rw [← mul_assoc, (factorsThrough hI hIt f n).extend_apply,
      (factorsThrough hI hIt f n).extend_apply, mul_pow, mul_assoc]
  dpow_mul m n x hx := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    simp only [(factorsThrough hI hIt f _).extend_apply]
    rw [mul_assoc, mul_comm _ (f _), ← mul_assoc (f _), ← _root_.map_mul,
      hI.dpow_mul _ _ (hIt ▸ mem_span_singleton_self t), _root_.map_mul, map_natCast]
    ring
  dpow_comp m n x hn hx := by
    obtain ⟨cx, rfl⟩ := (mem_map_span_singleton hIt).mp hx
    have hnt : hI.dpow n t ∈ I := dpow_mem hI hn (hIt ▸ mem_span_singleton_self t)
    simp only [hIt, mem_span_singleton'] at hnt
    obtain ⟨cnt, hcnt⟩ := hnt
    simp only
    rw [(factorsThrough hI hIt f _).extend_apply, ← hcnt, _root_.map_mul, ← mul_assoc]
    simp only [(factorsThrough hI hIt f _).extend_apply]
    rw [← mul_assoc, mul_comm _ (cx^_), ← map_natCast f, mul_assoc, ← _root_.map_mul,
      ← hI.dpow_comp _ hn (hIt ▸ mem_span_singleton_self t), ← hcnt,
      hI.dpow_smul _ (hIt ▸ mem_span_singleton_self t), _root_.map_mul, map_pow]
    ring

-- B-O Prop. 3.15
lemma extends_to_of_principal {J : Ideal A} (hJ : DividedPowers J) (hJp : Submodule.IsPrincipal J) :
    extends_to hJ f := by
  obtain ⟨t, ht⟩ := hJp
  use extension f ht hJ
  refine ⟨le_refl _, fun n a haJ ↦ ?_⟩
  rw [ht, submodule_span_eq, ← submodule_span_eq, Submodule.mem_span_singleton] at haJ
  obtain ⟨a, rfl⟩ := haJ
  simp only [extension]
  rw [smul_eq_mul, _root_.map_mul f, (factorsThrough hJ ht f n).extend_apply,
    dpow_smul _ _ (ht ▸ mem_span_singleton_self t), _root_.map_mul, map_pow]

end IsPrincipal

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
set_option linter.unusedVariables false in
lemma IsCompatibleWith_tfae {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I)
    {B : Type v} [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) :
    List.TFAE  [∃ hI' : DividedPowers (I.map f), isDPMorphism hI hI' f ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hI'.dpow n b = hJ.dpow n b,
      ∃ hK : DividedPowers (I.map f + J), isDPMorphism hI hK f ∧ isDPMorphism hJ hK (RingHom.id _),
      ∃ (K' : Ideal B) (hIJK : I.map f + J ≤ K') (hK' : DividedPowers K'),
      isDPMorphism hI hK' f ∧ isDPMorphism hJ hK' (RingHom.id _)] := by
  classical
  tfae_have 1 → 2
  · rintro ⟨hI', hII', hI'J⟩
    rw [inf_comm] at hI'J
    exact ⟨IdealAdd.dividedPowers hI' hJ hI'J,
      isDPMorphism.comp hI hI' (IdealAdd.dividedPowers hI' hJ hI'J) f
        (RingHom.id B) _ rfl (IdealAdd.isDPMorphism_left hI' hJ hI'J) hII',
      IdealAdd.isDPMorphism_right hI' hJ hI'J⟩
  tfae_have 2 → 3
  · rintro ⟨hK, hIK, hJK⟩
    use I.map f + J, le_refl _, hK
  tfae_have 3 → 1
  · rintro ⟨K, hIJK, hK, hIK, hJK⟩
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
      rw [if_pos hb', show hJ.dpow n b = hK.dpow n b by
        simpa only [RingHom.id_apply] using hJK.map_dpow n b hb]
  tfae_finish

-- TODO (maybe): use (2) instead
-- Or use 3.6 to construct this.
/-- B-0 Def 3.17 (using condition 1 of Prop. 3.16) -/
def IsCompatibleWith {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  ∃ hI' : DividedPowers (I.map f),
    (∀ (n : ℕ) (a : A), hI'.dpow n (f a) = f (hI.dpow n a)) ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hJ.dpow n b = hI'.dpow n b

end DividedPowers
