import DividedPowers.DPAlgebra.Dpow
import DividedPowers.ForMathlib.AlgebraComp

universe u v w

open DividedPowers Ideal DividedPowerAlgebra

def IsCompatibleWith {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] {J : Ideal B} (hJ : DividedPowers J) (f : A →+* B) : Prop :=
  ∃ hI' : DividedPowers (I.map f),
    (∀ (n : ℕ) (a : A), hI'.dpow n (f a) = f (hI.dpow n a)) ∧
      ∀ (n : ℕ) (b : B) (_ : b ∈ J ⊓ I.map f), hJ.dpow n b = hI'.dpow n b
#align is_compatible_with IsCompatibleWith

-- I added hext (compatibility condition) and replaced `g` `h` and `h_comp` by 
-- `[algebra A C] [algebra B C] [is_scalar_tower A B C]`
def IsUniversal {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v}
    [CommRing B] [Algebra A B] (J : Ideal B) {D : Type v} [CommRing D] (J' : Ideal D)
    (hJ' : DividedPowers J') (ψ : B →+* D) (_ : J.map ψ ≤ J') :=
  ∀ (C : Type w) [CommRing C],
    ∀ [Algebra A C] [Algebra B C],
      ∀ [IsScalarTower A B C],
        ∀ (K : Ideal C) (hK : DividedPowers K)
          -- (g : pd_morphism hI hK) 
          -- (h : B →+* C)
          (_ : J.map (algebraMap B C) ≤ K)
          -- (hcomp : h ∘ (algebra_map A B) = algebra_map A C)
          (_ : IsCompatibleWith hI hK (algebraMap A C)),
          ∃! φ : dpMorphism hJ' hK, φ.toRingHom ∘ ψ = algebraMap B C
#align is_universal IsUniversal

namespace DividedPowerEnvelope

variable {A : Type u} [CommRing A] {I : Ideal A} (hI : DividedPowers I) {B : Type v} [CommRing B]
  [Algebra A B] (J : Ideal B)

section Included

open DividedPowers DividedPowerAlgebra

variable (hIJ : I.map (algebraMap A B) ≤ J)

inductive rel1 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  | Rel {x : J} : rel1 (DividedPowerAlgebra.ι B J x) (algebraMap _ _ (x : B))
#align divided_power_envelope.rel1 DividedPowerEnvelope.rel1

set_option linter.uppercaseLean3 false
noncomputable def j1 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel1 J)
#align divided_power_envelope.J1 DividedPowerEnvelope.j1

inductive rel2 : Rel (DividedPowerAlgebra B J) (DividedPowerAlgebra B J)
  |
  Rel {x : I} {n : ℕ} :
    rel2 (dp B n (⟨algebraMap A B x, hIJ (Ideal.mem_map_of_mem _ x.2)⟩ : J))
      (algebraMap _ _ (algebraMap A B (dpow hI n x)))
#align divided_power_envelope.rel2 DividedPowerEnvelope.rel2

set_option linter.uppercaseLean3 false
noncomputable def j2 : Ideal (DividedPowerAlgebra B J) :=
  ofRel (rel2 hI J hIJ)
#align divided_power_envelope.J2 DividedPowerEnvelope.j2

noncomputable def j12 : Ideal (DividedPowerAlgebra B J) :=
  j1 J + j2 hI J hIJ
#align divided_power_envelope.J12 DividedPowerEnvelope.j12

theorem j12_isSubDPIdeal [DecidableEq B] :
    isSubDPIdeal (DividedPowerAlgebra.dividedPowers' B J)
      (j12 hI J hIJ ⊓ DividedPowerAlgebra.augIdeal B J) :=
  sorry
#align divided_power_envelope.J12_is_sub_pd_ideal DividedPowerEnvelope.j12_isSubDPIdeal

def DpEnvelopeOfIncluded : Type v :=
  DividedPowerAlgebra B J ⧸ j12 hI J hIJ
#align divided_power_envelope.dp_envelope_of_included DividedPowerEnvelope.DpEnvelopeOfIncluded

noncomputable instance : CommRing (DpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.commRing _

noncomputable instance : Algebra B (DpEnvelopeOfIncluded hI J hIJ) :=
  Ideal.Quotient.algebra _

noncomputable instance algebraOfIncluded : Algebra A (DpEnvelopeOfIncluded hI J hIJ) :=
  Algebra.comp A B (DpEnvelopeOfIncluded hI J hIJ)
#align divided_power_envelope.algebra_of_included DividedPowerEnvelope.algebraOfIncluded

instance isScalarTower_of_included : IsScalarTower A B (DpEnvelopeOfIncluded hI J hIJ) :=
  IsScalarTower.comp A B (DpEnvelopeOfIncluded hI J hIJ)
#align divided_power_envelope.is_scalar_tower_of_included DividedPowerEnvelope.isScalarTower_of_included

noncomputable def dpIdealOfIncluded [DecidableEq B] : Ideal (DpEnvelopeOfIncluded hI J hIJ) :=
  map (Ideal.Quotient.mk (j12 hI J hIJ)) (DividedPowerAlgebra.augIdeal B J)
#align divided_power_envelope.dp_ideal_of_included DividedPowerEnvelope.dpIdealOfIncluded

theorem sub_ideal_dpIdealOfIncluded [DecidableEq B] :
    J.map (algebraMap B (DpEnvelopeOfIncluded hI J hIJ)) ≤ dpIdealOfIncluded hI J hIJ :=
  by
  intro x hx
  rw [dpIdealOfIncluded]
  rw [Ideal.mem_map_iff_of_surjective]
  sorry
  exact Quotient.mk_surjective
#align divided_power_envelope.sub_ideal_dp_ideal_of_included DividedPowerEnvelope.sub_ideal_dpIdealOfIncluded

--TODO : fix
/- theorem dpEnvelopeOfIncluded_isUniversal [DecidableEq B] :
    IsUniversal hI J (dpIdealOfIncluded hI J hIJ)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B J) (j12_isSubDPIdeal hI J hIJ))
      (algebraMap B (DpEnvelopeOfIncluded hI J hIJ)) (sub_ideal_dpIdealOfIncluded hI J hIJ) :=
  sorry
#align divided_power_envelope.dp_envelope_of_included_is_universal 
  DividedPowerEnvelope.dpEnvelopeOfIncluded_isUniversal
 -/
end Included

section General

variable (I)

set_option linter.uppercaseLean3 false
def j' : Ideal B :=
  J + I.map (algebraMap A B)
#align divided_power_envelope.J' DividedPowerEnvelope.j'

theorem sub_ideal_j' : I.map (algebraMap A B) ≤ j' I J :=
  le_sup_of_le_right (le_refl _)
#align divided_power_envelope.sub_ideal_J' DividedPowerEnvelope.sub_ideal_j'

variable {I}

def DpEnvelope : Type v :=
  DividedPowerAlgebra B (j' I J) ⧸ j12 hI (j' I J) (sub_ideal_j' I J)
#align divided_power_envelope.dp_envelope DividedPowerEnvelope.DpEnvelope

noncomputable instance : CommRing (DpEnvelope hI J) :=
  Ideal.Quotient.commRing _

noncomputable instance : Algebra B (DpEnvelope hI J) :=
  Ideal.Quotient.algebra _

noncomputable instance algebra' : Algebra A (DpEnvelope hI J) :=
  Algebra.comp A B (DpEnvelope hI J)
#align divided_power_envelope.algebra' DividedPowerEnvelope.algebra'

instance : IsScalarTower A B (DpEnvelope hI J) :=
  IsScalarTower.comp A B (DpEnvelope hI J)

noncomputable def dpIdeal [DecidableEq B] : Ideal (DpEnvelope hI J) :=
  Ideal.map (Ideal.Quotient.mk (j12 hI (j' I J) (sub_ideal_j' I J)))
    (DividedPowerAlgebra.augIdeal B (j' I J))
#align divided_power_envelope.dp_ideal DividedPowerEnvelope.dpIdeal

theorem sub_ideal_dpIdeal [DecidableEq B] : 
    J.map (algebraMap B (DpEnvelope hI J)) ≤ dpIdeal hI J :=
  sorry
#align divided_power_envelope.sub_ideal_dp_ideal DividedPowerEnvelope.sub_ideal_dpIdeal

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

#exit 


theorem dpEnvelope_isUniversal [DecidableEq B] :
    IsUniversal hI J (dpIdeal hI J)
      (Quotient.dividedPowers (DividedPowerAlgebra.dividedPowers' B (j' I J))
        (j12_isSubDPIdeal hI (j' I J) (sub_ideal_j' I J)))
      (algebraMap B (DpEnvelope hI J)) (sub_ideal_dpIdeal hI J) :=
  by
  rw [IsUniversal]
  intro C _ _ _ _ K hK hJK hcomp
  obtain ⟨hI', hI'_ext, hI'_int⟩ := hcomp
  skip
  set K1 : Ideal C := K + I.map (algebraMap A C) with hK1
  set h1 : DividedPowers K1 := ideal_add.divided_powers hK hI' hI'_int with h1_def
  set g' : hI.pd_morphism h1 :=
    { toRingHom := algebraMap A C
      ideal_comp := le_sup_of_le_right (le_refl _)
      dpow_comp := fun n a ha =>
        by
        -- TODO: add rw lemma for ideal_add.divided_powers.dpow = ideal_add.dpow
        rw [← hI'_ext]
        exact ideal_add.dpow_eq_of_mem_right _ _ hI'_int _ (mem_map_of_mem (algebraMap A C) ha) }
  have hg' : (J' I J).map (algebraMap B C) ≤ K1 :=
    by
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
    exact ideal_add.dpow_eq_of_mem_right _ _ hI'_int _ hc
  obtain ⟨φ, hφ, hφ_unique⟩ :=
    dp_envelope_of_included_is_universal hI (J' I J) (sub_ideal_J' I J) C _ h1 hg' hI1
  -- TODO: generalize (map to sub-pd-structure)
  set ψ :
    (quotient.divided_powers (DividedPowerAlgebra.dividedPowers' B (J' I J))
          (J12_is_sub_pd_ideal hI (J' I J) (sub_ideal_J' I J))).DPMorphism
      hK :=
    { toRingHom := φ.to_ring_hom
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
  · sorry
#align divided_power_envelope.dp_envelope_is_universal DividedPowerEnvelope.dpEnvelope_isUniversal

