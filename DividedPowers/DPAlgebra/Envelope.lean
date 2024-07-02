import DividedPowers.DPAlgebra.Dpow
--import DividedPowers.ForMathlib.AlgebraComp -- TODO: We should not use this

universe u v w

open DividedPowers Ideal DividedPowerAlgebra

/-- B-0 Def 3.17 (using condition 1 of Prop. 3.16) -/
def IsCompatibleWith {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  ∃ hI' : DividedPowers (I.map f),
    (∀ (n : ℕ) (a : A), hI'.dpow n (f a) = f (hI.dpow n a)) ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hJ.dpow n b = hI'.dpow n b

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
          ∃! φ : dpMorphism hJ' hK, φ.toRingHom ∘ ψ = algebraMap B C

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
          ∃! φ : dpMorphism hJ' hK, φ.toRingHom ∘ ψ = algebraMap B C

-- TODO: universes?

namespace DividedPowerEnvelope

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v} [CommRing B]
  [Algebra A B] (J : Ideal B)

-- Case 1 of the proof, B-O pg 61 in pdf
section Included

open DividedPowers DividedPowerAlgebra

-- We assume that `f(I) ⊆ J`. (`f = algebraMap A B`)
variable (hIJ : I.map (algebraMap A B) ≤ J)

-- (DividedPowerAlgebra.ι B J x) is the map φ in B-O
-- (i)
inductive rel1 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : J} : rel1 (ι B J x) (algebraMap _ _ (x : B))

-- J1
noncomputable def J1 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel1 J)

-- (ii)
inductive rel2 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2 (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (algebraMap _ _ (algebraMap A B (dpow hI n x)))

lemma foo (x : I) {n : ℕ} (hn : n ≠ 0) : algebraMap _ _ (algebraMap A B (dpow hI n x)) ∈ J := by
  apply hIJ
  simp only [Algebra.id.map_eq_id, RingHomCompTriple.comp_apply]
  exact Ideal.mem_map_of_mem _ (dpow_mem _ hn x.2)

-- (ii)'
inductive rel2' : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : I} {n : ℕ} (hn : n ≠ 0) :
    rel2' (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (ι B J ⟨(algebraMap _ _ (algebraMap A B (dpow hI n x))), foo hI J hIJ x hn⟩)

-- J2
noncomputable def J2 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel2 hI J hIJ)

-- J in B-O
noncomputable def J12 : Ideal (DividedPowerAlgebra B J) :=
  J1 J + J2 hI J hIJ

-- B-O : Claim in pg 61, proof in pg 62
theorem J12_isSubDPIdeal [DecidableEq B] :
    isSubDPIdeal (DividedPowerAlgebra.dividedPowers' B J)
      (J12 hI J hIJ ⊓ DividedPowerAlgebra.augIdeal B J) :=
  sorry

-- 𝒟 at the end of pg 62 in B-O
def DPEnvelopeOfIncluded : Type v :=
  DividedPowerAlgebra B J ⧸ J12 hI J hIJ

noncomputable instance : CommRing (DPEnvelopeOfIncluded hI J hIJ) :=
  Quotient.commRing (J12 hI J hIJ)
  --Ideal.Quotient.commRing _

noncomputable instance : Algebra B (DPEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.algebra _

noncomputable instance algebraOfIncluded : Algebra A (DPEnvelopeOfIncluded hI J hIJ) :=
  ((algebraMap B (DPEnvelopeOfIncluded hI J hIJ)).comp (algebraMap A B)).toAlgebra

instance isScalarTower_of_included : IsScalarTower A B (DPEnvelopeOfIncluded hI J hIJ) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

-- J_bar in B-O
noncomputable def dpIdealOfIncluded [DecidableEq B] : Ideal (DPEnvelopeOfIncluded hI J hIJ) :=
  map (Ideal.Quotient.mk (J12 hI J hIJ)) (DividedPowerAlgebra.augIdeal B J)

-- J_bar has DP
theorem sub_ideal_dpIdealOfIncluded [DecidableEq B] :
    J.map (algebraMap B (DPEnvelopeOfIncluded hI J hIJ)) ≤ dpIdealOfIncluded hI J hIJ := by
  intro x hx
  rw [dpIdealOfIncluded]
  rw [Ideal.mem_map_iff_of_surjective]
  sorry
  exact Quotient.mk_surjective

-- End of case 1
theorem dpEnvelopeOfIncluded_IsWeakDPEnvelope [DecidableEq B] :
    IsWeakDPEnvelope hI J (dpIdealOfIncluded hI J hIJ)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J) (J12_isSubDPIdeal hI J hIJ))
      (algebraMap B (DPEnvelopeOfIncluded hI J hIJ)) (sub_ideal_dpIdealOfIncluded hI J hIJ) :=
  sorry

end Included

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
def DPEnvelope : Type v :=
  DividedPowerAlgebra B (J' I J) ⧸ J12 hI (J' I J) (sub_ideal_J' I J)

noncomputable instance : CommRing (DPEnvelope hI J) :=
  Ideal.Quotient.commRing _

noncomputable instance : Algebra B (DPEnvelope hI J) :=
  Ideal.Quotient.algebra _

noncomputable instance algebra' : Algebra A (DPEnvelope hI J) :=
  ((algebraMap B (DPEnvelope hI J)).comp (algebraMap A B)).toAlgebra

noncomputable instance algebra'' : Algebra (DividedPowerAlgebra B (J' I J)) (DPEnvelope hI J) :=
  Ideal.Quotient.algebra _

instance : IsScalarTower A B (DPEnvelope hI J) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

variable [DecidableEq B]

-- J₁_bar
noncomputable def J₁_bar : Ideal (DPEnvelope hI J) :=
  dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J)

-- The divided power structure on the DP envelope associated to `J₁_bar hI J`.
noncomputable def dividedPowers' : DividedPowers (J₁_bar hI J) :=
  Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
    (J12_isSubDPIdeal hI (J' I J) (sub_ideal_J' I J))
/-
lemma J_le_augIdeal :
    J.map (algebraMap B (DividedPowerAlgebra B (J' I J))) ≤ (augIdeal B ↥(J' I J)) := sorry

noncomputable def dpIdeal' : (dividedPowers' B ↥(J' I J)).SubDPIdeal :=
  SubDPIdeal.generatedDpow (DividedPowerAlgebra.dividedPowers' B (J' I J)) (J_le_augIdeal J) -/

lemma J_le_J₁_bar : (map (algebraMap B (DPEnvelope hI J)) J) ≤ (J₁_bar hI J) := by
  have heq : algebraMap B (DPEnvelope hI J) =
    (algebraMap (DividedPowerAlgebra B ↥(J' I J)) (DPEnvelope hI J)).comp
      (algebraMap B (DividedPowerAlgebra B ↥(J' I J))) := rfl
  rw [J₁_bar, dpIdealOfIncluded, heq, ← Ideal.map_map]
  apply map_mono
  intro x hx
  sorry

-- J_bar in pg 63 of B-O
noncomputable def dpIdeal : (dividedPowers' hI J).SubDPIdeal :=
  SubDPIdeal.generatedDpow (dividedPowers' hI J) (J_le_J₁_bar hI J)

-- First claim in Theorem 3.19 : `J⬝D_{B, γ} ⊆ J_bar`.
theorem sub_ideal_dpIdeal [DecidableEq B] :
    J.map (algebraMap B (DPEnvelope hI J)) ≤ (dpIdeal hI J).carrier := by
  rw [dpIdeal, SubDPIdeal.generatedDpow_carrier]
  intros x hx
  apply subset_span
  use 1, one_ne_zero, x, hx, (dpow_one _ (J_le_J₁_bar _ _ hx)).symm

noncomputable def dividedPowers [∀ x, Decidable (x ∈  (dpIdeal hI J).carrier)] :
    DividedPowers (dpIdeal hI J).carrier :=
  isSubDPIdeal.dividedPowers (dividedPowers' hI J) (dpIdeal hI J).toIsSubDPIdeal

-- I am not sure this is the right approach
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
        (Set.univ : Set (Fin hc.choose)).prod fun i => hI.dpow (Multiset.count i k) (hgi i).choose -/
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
    IsCompatibleWith hI (dividedPowers hI J) (algebraMap A (DPEnvelope hI J)) := by
  rw [IsCompatibleWith]
  sorry
section
-- TODO: move to IdealAdd file
variable {J} in
theorem IdealAdd.dividedPowers_dpow_eq_algebraMap (hJ : DividedPowers J)
    (hI' : DividedPowers (map (algebraMap A B) I))
    (hI'_ext : ∀ (n : ℕ) (a : A), hI'.dpow n ((algebraMap A B) a) = (algebraMap A B) (hI.dpow n a))
    (hI'_int : ∀ (n : ℕ), ∀ b ∈ J ⊓ map (algebraMap A B) I, hJ.dpow n b = hI'.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers hJ hI' hI'_int).dpow n ((algebraMap A B) a) =
      (algebraMap A B) (hI.dpow n a) := by
  rw [← hI'_ext]
  exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebraMap A B) ha)

-- Universal property claim of Theorem 3.19
theorem dpEnvelope_IsDPEnvelope [DecidableEq B]  [∀ x, Decidable (x ∈  (dpIdeal hI J).carrier)] :
    IsDPEnvelope hI J (dpIdeal hI J)
      (dividedPowers hI J)
      (algebraMap B (DPEnvelope hI J)) (sub_ideal_dpIdeal hI J) := by
  rw [IsDPEnvelope]
  rintro C _ _ _ _ K hK hJK ⟨hI', hI'_ext, hI'_int⟩
  -- K1 in page 63 of B-O
  set K1 : Ideal C := K + I.map (algebraMap A C) with hK1
  -- δ' in page 63 of B-O
  set h1 : DividedPowers K1 := IdealAdd.dividedPowers hK hI' hI'_int with h1_def
  set g' : hI.dpMorphism h1 :=
    { toRingHom  := algebraMap A C
      ideal_comp := le_sup_of_le_right (le_refl _)
      dpow_comp  := fun n a ha =>
        IdealAdd.dividedPowers_dpow_eq_algebraMap hI hK hI' hI'_ext hI'_int _ _ ha}
  have hg' : (J' I J).map (algebraMap B C) ≤ K1 := by
    rw [J', Ideal.add_eq_sup, Ideal.map_sup, sup_le_iff]
    refine ⟨le_trans hJK (le_sup_of_le_left (le_refl _)), ?_⟩
    · rw [Ideal.map_map, Eq.symm (IsScalarTower.algebraMap_eq A B C)]
      exact le_sup_of_le_right (le_refl _)
  have hI1 : IsCompatibleWith hI h1 (algebraMap A C) := by
    rw [IsCompatibleWith]
    use hI'; use hI'_ext
    intro n c hc
    simp only [hK1, Ideal.add_eq_sup, inf_of_le_right, le_sup_right] at hc
    exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int _ hc
  obtain ⟨φ, hφ, hφ_unique⟩ := by
    refine dpEnvelopeOfIncluded_IsWeakDPEnvelope hI (J' I J) (sub_ideal_J' I J) C _ h1 hg' ?_ hI1
    sorry

  -- TODO: generalize (map to sub-pd-structure)
  set ψ : (dividedPowers hI J).dpMorphism hK :=
    { toRingHom  := φ.toRingHom
      ideal_comp := by
        have := φ.ideal_comp
        have hKK1 : K ≤ K1 := sorry
        intros x hx
        --simp? at hx

        have hx' : x ∈ map φ.toRingHom (dpIdealOfIncluded hI (J' I J) (sub_ideal_J' I J)) := sorry
        specialize this
        sorry

      dpow_comp  := fun n a ha => by
        have := φ.dpow_comp
        obtain ⟨r, s⟩ := hI1
        --rw ← hI'_ext,
        --rw φ.dpow_comp,
        sorry }
  use ψ
  --simp only,
  use hφ
  intro α hα

  set β : (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B ↥(J' I J))
    (J12_isSubDPIdeal hI (J' I J) (sub_ideal_J' I J))).dpMorphism h1 :=
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
      simp only [DPEnvelope] -/

      sorry
    dpow_comp  := fun n a ha => by
      obtain ⟨hK', hmap, hint⟩ := hI1
      --rw [← hα] at hmap
      simp_rw [← hI'_ext] at hmap
      --rw φ.dpow_comp,
      sorry }

  have hβ : β.toRingHom ∘ ⇑(algebraMap B (DPEnvelopeOfIncluded hI (J' I J)
    (sub_ideal_J' I J))) = ⇑(algebraMap B C) := sorry

  ext x
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [← hφ_unique β hβ]


#exit

theorem dpEnvelope_IsDPEnvelope [DecidableEq B] :
    IsDPEnvelope hI J (dpIdeal hI J)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B (J' I J))
        (J12_isSubDPIdeal hI (J' I J) (sub_ideal_J' I J)))
      (algebraMap B (DPEnvelope hI J)) (sub_ideal_dpIdeal hI J) := by
  rw [IsDPEnvelope]
  rintro C _ _ _ _ K hK hJK ⟨hI', hI'_ext, hI'_int⟩
  -- K1 in page 63 of B-O
  set K1 : Ideal C := K + I.map (algebraMap A C) with hK1
  -- δ' in page 63 of B-O
  set h1 : DividedPowers K1 := IdealAdd.dividedPowers hK hI' hI'_int with h1_def
  set g' : hI.dpMorphism h1 :=
    { toRingHom  := algebraMap A C
      ideal_comp := le_sup_of_le_right (le_refl _)
      dpow_comp  := fun n a ha =>
        IdealAdd.dividedPowers_dpow_eq_algebraMap hI hK hI' hI'_ext hI'_int _ _ ha}
  have hg' : (J' I J).map (algebraMap B C) ≤ K1 := by
    rw [J', Ideal.add_eq_sup, Ideal.map_sup, sup_le_iff]
    refine ⟨le_trans hJK (le_sup_of_le_left (le_refl _)), ?_⟩
    · rw [Ideal.map_map, Eq.symm (IsScalarTower.algebraMap_eq A B C)]
      exact le_sup_of_le_right (le_refl _)
  have hI1 : IsCompatibleWith hI h1 (algebraMap A C) := by
    rw [IsCompatibleWith]
    use hI'; use hI'_ext
    intro n c hc
    simp only [hK1, Ideal.add_eq_sup, inf_of_le_right, le_sup_right] at hc
    exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int _ hc
  obtain ⟨φ, hφ, hφ_unique⟩ := by
    refine dpEnvelopeOfIncluded_IsWeakDPEnvelope hI (J' I J) (sub_ideal_J' I J) C _ h1 hg' ?_ hI1
    sorry
  -- TODO: generalize (map to sub-pd-structure)
  set ψ :
    (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B (J' I J))
          (J12_isSubDPIdeal hI (J' I J) (sub_ideal_J' I J))).dpMorphism
      hK :=
    { toRingHom := φ.toRingHom
      ideal_comp := sorry
      dpow_comp := fun n a ha => by
        obtain ⟨r, s⟩ := hI1
        --rw ← hI'_ext,
        --rw φ.dpow_comp,
        sorry }
  use ψ
  --simp only,
  use hφ
  intro α hα
  ext x
  rw [← hα] at hφ
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  ·--have := hφ_unique (ideal_add.divided_powers α hI'),
    sorry
  --· sorry


/- def dividedPowers_of_map {C : Type*} [CommRing C] (f : A →+* C) [∀ c, Decidable (c ∈ map f I)] :
  DividedPowers (I.map f) :=
{ dpow      := fun n c ↦ by
    by_cases hc : c ∈ I.map f
    · rw [Ideal.map] at hc
      --squeeze_simp at hc,
      --apply submodule.span_induction _ _ _ _ hc,
      sorry
    · exact 0
  dpow_null := sorry
  dpow_zero := sorry
  dpow_one  := sorry
  dpow_mem  := sorry
  dpow_add  := sorry
  dpow_smul := sorry
  dpow_mul  := sorry
  dpow_comp := sorry }

end -/
