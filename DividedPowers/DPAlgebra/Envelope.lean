import DividedPowers.DPAlgebra.Dpow
--import DividedPowers.ForMathlib.AlgebraComp -- TODO: We should not use this

universe u v w

open DividedPowers Ideal DividedPowerAlgebra

/-- B-0 Def 3.17 -/
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

instance : IsScalarTower A B (DPEnvelope hI J) :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

noncomputable def dpIdeal [DecidableEq B] : Ideal (DPEnvelope hI J) :=
  Ideal.map (Ideal.Quotient.mk (J12 hI (J' I J) (sub_ideal_J' I J)))
    (DividedPowerAlgebra.augIdeal B (J' I J))
#align divided_power_envelope.dp_ideal DividedPowerEnvelope.dpIdeal

theorem sub_ideal_dpIdeal [DecidableEq B] :
    J.map (algebraMap B (DPEnvelope hI J)) ≤ dpIdeal hI J :=
  sorry

section

/- def divided_powers_of_map {C : Type*} [comm_ring C] (f : A →+* C) [∀ c, decidable (c ∈ map f I)] :
  divided_powers (I.map f) :=
{ dpow      := λ n c,
  begin
    by_cases hc : c ∈ I.map f,
    { rw ideal.map at hc,
      --squeeze_simp at hc,
      --apply submodule.span_induction _ _ _ _ hc,
      sorry },
    { exact 0}
  end,
  dpow_null := sorry,
  dpow_zero := sorry,
  dpow_one  := sorry,
  dpow_mem  := sorry,
  dpow_add  := sorry,
  dpow_smul := sorry,
  dpow_mul  := sorry,
  dpow_comp := sorry }


end -/

/- lemma bar (hK : DividedPowers K) :
  (IdealAdd.dividedPowers hK hI' hI'_int).dpow n ((algebraMap A C) a) =
      hI'.dpow n ((algebraMap A C) a) :=
  sorry -/

theorem extracted_1 (C : Type*) [CommRing C] [Algebra A C]  (K : Ideal C) (hK : DividedPowers K)
    (hI' : DividedPowers (map (algebraMap A C) I))
    (hI'_ext : ∀ (n : ℕ) (a : A), hI'.dpow n ((algebraMap A C) a) = (algebraMap A C) (hI.dpow n a))
    (hI'_int : ∀ (n : ℕ), ∀ b ∈ K ⊓ map (algebraMap A C) I, hK.dpow n b = hI'.dpow n b)
    (n : ℕ) (a : A) (ha : a ∈ I) :
     (IdealAdd.dividedPowers hK hI' hI'_int).dpow n ((algebraMap A C) a) =
      (algebraMap A C) (hI.dpow n a) := by
  rw [← hI'_ext]
  exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebraMap A C) ha)


theorem dpEnvelope_IsDPEnvelope [DecidableEq B] :
    IsDPEnvelope hI J (dpIdeal hI J)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B (J' I J))
        (J12_isSubDPIdeal hI (J' I J) (sub_ideal_J' I J)))
      (algebraMap B (DPEnvelope hI J)) (sub_ideal_dpIdeal hI J) := by
  rw [IsDPEnvelope]
  intro C _ _ _ _ K hK hJK hcomp
  obtain ⟨hI', hI'_ext, hI'_int⟩ := hcomp
  skip
  set K1 : Ideal C := K + I.map (algebraMap A C) with hK1
  set h1 : DividedPowers K1 := IdealAdd.dividedPowers hK hI' hI'_int with h1_def
  set g' : hI.dpMorphism h1 :=
    { toRingHom := algebraMap A C
      ideal_comp := le_sup_of_le_right (le_refl _)
      dpow_comp := fun n a ha => by
        -- TODO: add rw lemma for ideal_add.divided_powers.dpow = ideal_add.dpow
        rw [← hI'_ext]
        exact IdealAdd.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebraMap A C) ha) }
  have hg' : (J' I J).map (algebraMap B C) ≤ K1 := by
    rw [J']
    rw [Ideal.add_eq_sup]
    rw [Ideal.map_sup]
    rw [sup_le_iff]
    constructor
    · exact le_trans hJK (le_sup_of_le_left (le_refl _))
    · have halg : (algebraMap B C).comp (algebraMap A B) = algebraMap A C := by sorry
      rw [Ideal.map_map, halg]
      exact le_sup_of_le_right (le_refl _)
  have hI1 : IsCompatibleWith hI h1 (algebraMap A C) :=
    by
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
  -- TODO: add rw lemma for ideal_add.divided_powers.dpow = ideal_add.dpow
  /- rw ← hI'_ext,
        exact ideal_add.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebra_map A C) ha), -/
  use ψ
  --simp only,
  use hφ
  intro α hα
  ext
  ·--have := hφ_unique (ideal_add.divided_powers α hI'),
    sorry
  --· sorry
