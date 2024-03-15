import DividedPowers.PolynomialMap.Basic
import DividedPowers.ForMathlib.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Lift the definition of a `PolynomialMap` to higher universes

Consider a commutative semiring `R` and two `R`-modules `M` and `N`.
Although written naïvely, the definition of a `f : PolynomialMap R M N`
presents is as a universal definition of maps
`f.toFun' :  S ⊗[R] M → S ⊗[R] N`,
where `S` ranges over commutative `R`-algebras,
related by compatibility equalities
`h.isCompat' : f.toLinearMap.rTensor N ∘ f.toFun' S = f.toFun' S' ∘ h.toLinearMap.rTensor M`,
for all `h : S →ₐ[R] S'`.
To be correct, the definition restricts these algebras `S`
to live in the same universe as `R`.
The present file extends the definitions to all universes.

* `PolynomialMap.toFun` is the variant of `PolynomialMap.toFun'`
without any universe restrictions.

* `PolynomialMap.isCompat` and `PolynomialMap.isCompat_apply` are
the variants of `PolynomialMap.isCompat` without any universe restrictions.

* Finally, we show the compatibility with the basic constructions
  on polynomial maps (module structure, composition).

## Construction

The idea is standard, setting it up in detail is sometimes technical.

Consider `f : PolynomialMap R M N` and a general commutative algebra `S`.
Any tensor `t : S ⊗[R] M` is induced from a tensor `u : B ⊗[R] M`,
where `B` is a finite type subalgebra of `S`.
Taking generators, we present `B` as the range of an algebra morphism
`φ : MvPolynomial (Fin n) R →ₐ[R] S`, for some integer `n`,
and get `p : MvPolynomial (Fin n) R ⊗[R] M` such that
`φ.toLinearMap.rTensor M p = t`.
We set `f.toFun t = φ.toLinearMap.rTensor N (f.toFun p)`.
This is forced by the expected compatibility property `f.isCompat`.

We then prove that it does not depend on choices
and satisfies the compatibility property `f.isCompat`.

`PolynomialMap.toFun_eq_toFun'` proves that it extends `f.toFun'`.

## TODO

* Because we use direct limits, we have to work on commutative rings.
A standard refactor of the files about direct limits
will extend this (automatically) to commutative semirings.

-/

universe u v

variable {R : Type u} [CommRing R]
  {M : Type _} [AddCommGroup M] [Module R M]
  {N : Type _} [AddCommGroup N] [Module R N]
  (f g : PolynomialMap R M N)

open TensorProduct LinearMap MvPolynomial

theorem AlgHom.comp_rangeRestrict
    {R S T : Type*} [CommSemiring R]
    [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    (φ : S →ₐ[R] T) :
    (Subalgebra.val _).comp φ.rangeRestrict = φ := by
  ext; rfl

theorem AlgHom.quotientKerEquivRange_mk
    {R S T : Type*} [CommRing R]
    [CommRing S] [Ring T] [Algebra R S] [Algebra R T]
    (φ : S →ₐ[R] T)  :
    (Ideal.quotientKerEquivRange φ).toAlgHom.comp
      (Ideal.Quotient.mkₐ R (RingHom.ker φ)) = φ.rangeRestrict := by
  ext s
  simp only [AlgEquiv.toAlgHom_eq_coe, coe_comp, AlgHom.coe_coe,
    Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, coe_codRestrict]
  rfl

theorem Ideal.kerLiftAlg_eq_val_comp_Equiv
    {R S T : Type*} [CommRing R] [CommRing S] [Semiring T]
    [Algebra R S] [Algebra R T] (φ : S →ₐ[R] T) :
    Ideal.kerLiftAlg φ
      = (Subalgebra.val _).comp (Ideal.quotientKerEquivRange φ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  ext s; simp; rfl

variable (R)
theorem MvPolynomial.aeval_range (S : Type*) [CommRing S] [Algebra R S] {σ : Type*} (s : σ → S) :
  (aeval (R := R) s).range = Algebra.adjoin R (Set.range s) := by
  apply le_antisymm
  · intro x
    rintro ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | h_C a =>
      simp only [aeval_C, Algebra.mem_adjoin_iff]
      apply Subring.subset_closure
      left
      use a
    | h_add p q hp hq => simp only [map_add]; exact Subalgebra.add_mem _ hp hq
    | h_X p n h =>
      simp [_root_.map_mul]
      apply Subalgebra.mul_mem _ h
      apply Algebra.subset_adjoin
      use n
  · rw [Algebra.adjoin_le_iff]
    intro x
    rintro ⟨i, rfl⟩
    use X i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

namespace PolynomialMap

variable (M)
variable (S : Type v) [CommRing S] [Algebra R S]
/-- The type of lifts of  `S ⊗[R] M` to a polynomial ring -/
private
def α : Type _ := Σ (s : Finset S), (MvPolynomial (Fin s.card) R) ⊗[R] M


variable {M S}
/-- The lift of f.toFun to the type `α` -/
private
noncomputable def φAux (s : Finset S) : MvPolynomial (Fin s.card) R →ₐ[R] S :=
  MvPolynomial.aeval  (R := R) (fun n ↦ (s.equivFin.symm n: S))

private
theorem φAux_eq_comp (s : Finset S) :
    φAux R s = (Ideal.kerLiftAlg (φAux R s)).comp
      (Ideal.Quotient.mkₐ R (RingHom.ker (φAux R s))) := by ext; rfl

private
theorem φAux_eq_comp' (s : Finset S) : φAux R s
    = (Subalgebra.val _).comp
        ((Ideal.quotientKerEquivRange (φAux R s)).toAlgHom.comp
          (Ideal.Quotient.mkₐ R (RingHom.ker (φAux R s)))) := by ext; rfl

private
theorem φAux_apply_X (s : Finset S) (n : Fin s.card) :
    φAux R s (X n) = s.equivFin.symm n := by
  simp only [φAux, aeval_X]

private
theorem φAux_range (s : Finset S) : (φAux R s).range = Algebra.adjoin R s := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on with
    | h_C r =>
      simp only [AlgHom.toRingHom_eq_coe, ← algebraMap_eq, RingHom.coe_coe, AlgHom.commutes]
      apply algebraMap_mem
    | h_add p q hp hq =>
      simp only [map_add]
      exact add_mem hp hq
    | h_X p n hp =>
      simp only [_root_.map_mul]
      apply mul_mem hp
      apply Algebra.subset_adjoin
      simp [φAux]
  · rw [Algebra.adjoin_le_iff]
    intro x
    simp only [Finset.mem_coe, φAux, AlgHom.coe_range, Set.mem_range]
    intro hx
    use X (s.equivFin ⟨x, hx⟩)
    simp

variable (M S)
/-- The projection from `α` to `S ⊗[R] M` -/
private
noncomputable def π : α R M S → S ⊗[R] M :=
  fun ⟨s, p⟩ ↦ rTensor M (φAux R s).toLinearMap p

variable {R M S}

private
noncomputable def φ :
    α R M S → S ⊗[R] N := fun ⟨s,p⟩ ↦
  rTensor N (φAux R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

variable (S)
noncomputable def toFun :
    S ⊗[R] M → S ⊗[R] N := by
  apply Function.extend (π R M S) (φ f) (fun _ ↦ 0)

theorem Subalgebra.val_comp_inclusion {R : Type*} [CommSemiring R]
    {S : Type*} [Semiring S] [Algebra R S]
    {A B : Subalgebra R S} (h : A ≤ B) :
  (Subalgebra.val B).comp (Subalgebra.inclusion h) = Subalgebra.val A := rfl

theorem rTensor_range {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] (f : M →ₗ[R] N) :
    LinearMap.range (f.rTensor P) =
    LinearMap.range ((Submodule.subtype (LinearMap.range f)).rTensor P) := by
  sorry

variable {S}
theorem Subalgebra.FG.exists_range_eq
    {B : Subalgebra R S} (hB : Subalgebra.FG B) :
    ∃ s : Finset S, (φAux R s).range = B := by
  choose s hs using hB
  use s
  simp only [φAux_range, hs]

theorem exists_lift_of_le_rTensor_range
    {R : Type*} [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T] (A : Subalgebra R T)
    {φ : S →ₐ[R] T} (hφ : A ≤ AlgHom.range φ)
    (t : T ⊗[R] M) (ht : t ∈ LinearMap.range ((Subalgebra.val A).toLinearMap.rTensor M)) :
    ∃ s : S ⊗[R] M, φ.toLinearMap.rTensor M s = t := by
  choose u hu using ht
  suffices Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    choose p hp using this ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu, ← Subalgebra.val_comp_inclusion hφ]
    simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [← hp]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    congr
  exact rTensor_surjective M (by exact AlgHom.rangeRestrict_surjective φ)

theorem π_surjective : Function.Surjective (π R M S) := by
  intro t
  choose B hB ht using TensorProduct.Algebra.exists_of_fg t
  choose s hs using Subalgebra.FG.exists_range_eq hB
  choose p hp using
    exists_lift_of_le_rTensor_range M B (le_of_eq hs.symm) t ht
  exact ⟨⟨s, p⟩, hp⟩

theorem toFun'_eq_of_diagram
    {T : Type w} [CommRing T] [Algebra R T]
    (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M)
    (t : Finset T) (q : MvPolynomial (Fin t.card) R ⊗[R] M)
    (h : S →ₐ[R] T)
    (h' : (φAux R s).range →ₐ[R] (φAux R t).range)
    (hh' : (Subalgebra.val (φAux R t).range).comp h'
        = h.comp (Subalgebra.val (φAux R s).range))
    (hpq : (rTensor M (h'.comp (φAux R s).rangeRestrict).toLinearMap) p
      = rTensor M (φAux R t).rangeRestrict.toLinearMap q) :
    LinearMap.rTensor N (h.comp (φAux R s)).toLinearMap
      (f.toFun' (MvPolynomial (Fin s.card) R) p)
    = LinearMap.rTensor N (φAux R t).toLinearMap
      (f.toFun' (MvPolynomial (Fin t.card) R) q) := by

  let θ := (Ideal.quotientKerEquivRange (R := R) (φAux R t)).symm.toAlgHom.comp
    (h'.comp (Ideal.quotientKerEquivRange (φAux R s)).toAlgHom)
  have ht : h.comp ((Subalgebra.val (AlgHom.range (φAux R s))).comp
    (Ideal.quotientKerEquivRange (φAux R s)).toAlgHom)
    = (Subalgebra.val (AlgHom.range (φAux R t))).comp
        ((Ideal.quotientKerEquivRange (φAux R t)).toAlgHom.comp θ) := by
    simp only [θ]
    simp only [← AlgHom.comp_assoc, ← hh']
    apply congr_arg₂ _ _ rfl
    apply congr_arg₂ _ _ rfl
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id]

  simp only [φAux_eq_comp', ← AlgHom.comp_assoc]
  nth_rewrite 2 [AlgHom.comp_assoc]
  rw [ht]
  simp only [AlgHom.comp_assoc]
  simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
  apply LinearMap.congr_arg
  apply LinearMap.congr_arg
  simp only [f.isCompat_apply']
  apply congr_arg
  simp only [θ]
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, AlgHom.comp_assoc]
  rw [AlgHom.quotientKerEquivRange_mk]
  simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
  simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply] at hpq
  rw [hpq]
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, AlgHom.comp_assoc]
  apply LinearMap.congr_fun
  apply congr_arg
  apply congr_arg
  ext n
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe, Function.comp_apply,
    Ideal.Quotient.mkₐ_eq_mk]
  erw [Equiv.symm_apply_eq]
  rfl

/-- Ce cas compare les deux formules lorsque les tenseurs se comparent
  dans une inclusion de sous-algèbres -/
private
theorem toFun'_eq_of_inclusion
    (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M)
    (s' : Finset S) (p' : MvPolynomial (Fin s'.card) R ⊗[R] M)
    (hss' : (φAux R s).range ≤ (φAux R s').range)
    (hpp' : LinearMap.rTensor M ((Subalgebra.inclusion hss').comp (φAux R s).rangeRestrict).toLinearMap p = LinearMap.rTensor M (φAux R s').rangeRestrict.toLinearMap p') :
    (LinearMap.rTensor N (AlgHom.toLinearMap (φAux R s)))
      (f.toFun' (MvPolynomial (Fin s.card) R) p)
    = (LinearMap.rTensor N (AlgHom.toLinearMap (φAux R s')))
        (f.toFun' (MvPolynomial (Fin s'.card) R) p') :=
  toFun'_eq_of_diagram f s p s' p' (AlgHom.id R S) (Subalgebra.inclusion hss')
    (by ext x; simp) hpp'

/-- Ce cas montrera que f.toFunAux S permet de définir f.toFun S t -/
/- theorem eq_of_eq (S : Type v) [CommRing S] [Algebra R S]
    (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M)
    (s' : Finset S) (p' : MvPolynomial (Fin s'.card) R ⊗[R] M)
    (h : LinearMap.rTensor M (φAux s).toLinearMap p =
          LinearMap.rTensor M (φAux s').toLinearMap p') :
    f.toFunAux s p = f.toFunAux s' p' := by-/

private
theorem φ_factorsThrough_π :
    Function.FactorsThrough (φ f) (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [φ]

  classical
  set u := LinearMap.rTensor M (φAux R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φAux R s).range := by
    rw [← Algebra.map_top]
    apply Subalgebra.FG.map
    exact (Algebra.FiniteType.mvPolynomial R (Fin s.card)).out

  set u' := LinearMap.rTensor M (φAux R s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φAux R s').range := by
    rw [← Algebra.map_top]
    apply Subalgebra.FG.map
    exact (Algebra.FiniteType.mvPolynomial R (Fin s'.card)).out

  have huu' : LinearMap.rTensor M (Subalgebra.val _).toLinearMap u =
    LinearMap.rTensor M (Subalgebra.val _).toLinearMap u' := by
    simp only [π] at h
    simp only [hu, hu', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← AlgHom.comp_toLinearMap,
      AlgHom.comp_rangeRestrict, h]

  obtain ⟨B, hAB, hA'B, hB, h⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq' (R := R) uFG u u'FG u' huu'
  let ⟨t, hB⟩ := hB
  rw [← φAux_range R t, eq_comm] at hB
  have hAB' : (φAux R s).range ≤ (φAux R t).range := le_trans hAB (le_of_eq hB)
  have hA'B' : (φAux R s').range ≤ (φAux R t).range := le_trans hA'B (le_of_eq hB)
  have : ∃ q : MvPolynomial (Fin t.card) R ⊗[R] M,
    LinearMap.rTensor M (AlgHom.toLinearMap (φAux R t).rangeRestrict) q
      = LinearMap.rTensor M ((Subalgebra.inclusion (le_of_eq hB)).comp (Subalgebra.inclusion hAB)).toLinearMap u := by
    suffices Function.Surjective (?_) by
      exact this _
    apply rTensor_surjective
    exact AlgHom.rangeRestrict_surjective _

  obtain ⟨q, hq⟩ := this
  rw  [toFun'_eq_of_inclusion f s p t q hAB', toFun'_eq_of_inclusion f s' p' t q hA'B']
  · rw [hq]
    simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [← hu', h]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    congr
  · rw [hq, hu]
    simp only [← LinearMap.comp_apply, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp]
    congr; ext; rfl

private
theorem toFun_apply
    {t : S ⊗[R] M} {a : α R M S} (ha : π R M S a = t)  :
    f.toFun S t = φ f a := by
  rw [PolynomialMap.toFun, ← ha, (φ_factorsThrough_π f).extend_apply]

theorem toFun_eq_toFun' (S : Type u) [CommRing S] [Algebra R S] :
    f.toFun S = f.toFun' S := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_apply ha, φ, f.isCompat_apply']
  apply congr_arg
  exact ha

theorem toFun_eq_toFun'_apply (S : Type u) [CommRing S] [Algebra R S] (t : S ⊗[R] M):
    f.toFun S t = f.toFun' S t :=
  congr_fun (f.toFun_eq_toFun' S) t

theorem isCompat_apply
    {T : Type w} [CommRing T] [Algebra R T] (h : S →ₐ[R] T) (t : S ⊗[R] M) :
    rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTensor M h.toLinearMap t) := by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h

  let h' : (φAux R s).range →ₐ[R] (φAux R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φAux R s').range (by
    rintro ⟨x, hx⟩
    simp only [φAux_range] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply]
    simp only [Finset.coe_image, Algebra.adjoin_image, s']
    exact ⟨x, hx, rfl⟩)

  let j : Fin s.card → Fin s'.card :=
    (s'.equivFin) ∘ (fun ⟨x, hx⟩ ↦ ⟨h x, Finset.mem_image_of_mem h hx⟩) ∘ (s.equivFin).symm
  have eq_h_comp : (φAux R s').comp (rename j) = h.comp (φAux R s) := by
    ext p
    simp only [φAux, AlgHom.comp_apply, aeval_rename, comp_aeval]
    congr
    ext n
    simp [j]

  let p' := rTensor M (rename j).toLinearMap  p
  have ha' : π R M T (⟨s', p'⟩ : α R M T) = rTensor M h.toLinearMap t := by
    simp only [← ha, π, p']
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    rw [eq_h_comp]

  rw [PolynomialMap.toFun_apply f ha]
  rw [PolynomialMap.toFun_apply f ha']
  simp only [φ]
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
  apply toFun'_eq_of_diagram f s p s' p' h h'
  · ext x; simp [h']
  · simp only [p']
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    apply LinearMap.congr_fun
    apply congr_arg
    apply congr_arg
    ext n
    simp [h', j, φAux_apply_X]

theorem isCompat
    {T : Type w} [CommRing T] [Algebra R T] (h : S →ₐ[R] T) :
    h.toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M := by
  ext t
  simp only [Function.comp_apply, PolynomialMap.isCompat_apply]

/-- Extension of `MvPolynomial.add_def_apply` -/
theorem add_toFun_apply (t : S ⊗[R] M) :
    (f + g).toFun S t = f.toFun S t + g.toFun S t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_apply _ ha, φ, add_def, map_add]

/-- Extension of `MvPolynomial.add_def` -/
theorem add_toFun : (f + g).toFun S = f.toFun S + g.toFun S := by
  ext t
  simp only [Pi.add_apply, add_toFun_apply]

/-- Extension of `MvPolynomial.zero_def` -/
theorem zero_toFun : (0 : PolynomialMap R M N).toFun S = 0 := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_apply _ ha, φ, zero_def, Pi.zero_apply, map_zero]

/-- Extension of `MvPolynomial.smul_def` -/
theorem smul_toFun (r : R) : (r • f).toFun S = r • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_apply _ ha, φ, smul_def, Pi.smul_apply, map_smul]

variable {P : Type*} [AddCommGroup P] [Module R P]
  (g : PolynomialMap R N P) (f : PolynomialMap R M N)

/-- Extension of `MvPolynomial.comp_toFun'` -/
theorem comp_toFun (S : Type*) [CommRing S] [Algebra R S] :
    (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialMap.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_apply _ ha, π, φ]
  simp only [Function.comp_apply]
  simp only [toFun_apply _ hb, φ]
  simp only [toFun_apply _ ha, φ, comp_toFun', Function.comp_apply]

theorem isCompat_apply_ground
    (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun S) (1 ⊗ₜ x) := by
  simp only [ground, ← toFun_eq_toFun']
  convert f.isCompat_apply (algebraMap' R S) (1 ⊗ₜ[R] x)
  simp only [Function.comp_apply, TensorProduct.lid_symm_apply]
  rw [TensorProduct.includeRight_lid]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, _root_.map_one]

/- Lemmas to allow to use the definition -/
/-- Lift an element of a tensor product -/
theorem exists_lift (t : S ⊗[R] M) :
    ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S) (p : MvPolynomial (Fin n) R ⊗[R] M),
      ψ.toLinearMap.rTensor M p = t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φAux R s, p, ha

theorem Subalgebra.fg_sup
    {R : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {A B : Subalgebra R S} (hA : A.FG) (hB : B.FG) :
    Subalgebra.FG (A ⊔ B) := by
  classical
  choose s hs using hA
  choose t ht using hB
  rw [← hs, ← ht, ← Algebra.adjoin_union, ← Finset.coe_union]
  exact ⟨s ∪ t, rfl⟩

theorem exists_lift' (t : S ⊗[R] M) (s : S) :
    ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
      (p : MvPolynomial (Fin n) R ⊗[R] M) (q : MvPolynomial (Fin n) R),
      ψ.toLinearMap.rTensor M p = t ∧ ψ q = s := by
  classical
  choose A hA ht using TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.fg_sup hA (Subalgebra.fg_adjoin_finset _)
  choose gen hgen using Subalgebra.FG.exists_range_eq hB
  have hAB : A ≤ A ⊔ Algebra.adjoin R ({s} : Finset S) := le_sup_left
  rw [← hgen] at hAB
  choose p hp using exists_lift_of_le_rTensor_range M _ hAB t ht
  have : s ∈ AlgHom.range (φAux R gen) := by
    rw [hgen]
    apply Algebra.subset_adjoin
    simp only [Finset.coe_singleton, Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
    right
    exact Algebra.subset_adjoin rfl
  choose q hq using this
  use gen.card, φAux R gen, p, q, hp, hq

end PolynomialMap
