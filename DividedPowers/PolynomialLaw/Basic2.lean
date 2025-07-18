/- Copyright ACL @ MIdFF 2024 -/

import DividedPowers.ForMathlib.RingTheory.TensorProduct.DirectLimit.FG
import DividedPowers.ForMathlib.RingTheory.Congruence.Hom

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Logic.Small.Set
import Mathlib.RingTheory.PolynomialLaw.Basic

/-! # Polynomial laws on modules

Let `M` and `N` be a modules over a commutative ring `R`.
A polynomial map `f : PolynomialLaw R M N`, with notation `f : M →ₚ[R] N`,
is a “law” that assigns, to every `R`-algebra `S`,
* a map `PolynomialLaw.toFun' f S : S ⊗[R] M → S ⊗[R] N`,
* compatibly with morphisms of `R`-algebras, as expressed by `PolynomialLaw.isCompat' f`

For type theoretic reasons, if `R : Type u`, then the definition of the polynomial map `f`
is restricted to `R`-algebras `S` such that `S : Type u`.
Using the fact that a module is the direct limit of its finitely generated submodules, that a
finitely generated subalgebra is a quotient of a polynomial ring in the universe `u`, plus
commutation of tensor products with direct limits, we extend the functor to all `R`-algebras.

## Main definitions/lemmas

* `PolynomialLaw.toFun` is the universal extension of `PolynomialLaw.toFun'`

* `PolynomialLaw.isCompat` is the universal extension of `PolynomialLaw.isCompat'`

* `PolynomialLaw.instModule : Module R (M →ₚ[R] N)` shows that polynomial maps form a `R`-module.

* `PolynomialLaw.ground f` is the map `M → N` corresponding to `PolynomialLaw.toFun' f R` under
  the isomorphisms `R ⊗[R] M ≃ₗ[R] M`, and similarly for `N`.

In further files, we construct the coefficients of a polynomial map and show the relation with
polynomials (when the module `M` is free and finite).

Reference : Roby, Norbert. 1963. « Lois polynomes et lois formelles en théorie des modules ».
Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348.
https://doi.org/10.24033/asens.1124.

## Construction of the universal extension

The idea of the universal extension is standard, setting it up in detail is sometimes technical.

Consider `f : PolynomialLaw R M N` and a general commutative algebra `S`. Any tensor `t : S ⊗[R] M`
is induced from a tensor `u : B ⊗[R] M`, where `B` is a finite type subalgebra of `S`.
Taking generators, we present `B` as the range of an algebra morphism
`φ : MvPolynomial (Fin n) R →ₐ[R] S`, for some integer `n`, and get
`p : MvPolynomial (Fin n) R ⊗[R] M` such that `φ.toLinearMap.rTensor M p = t`.
We set `f.toFun t = φ.toLinearMap.rTensor N (f.toFun p)`. This is forced by the expected
compatibility property `f.isCompat`. We then prove that it does not depend on choices and
satisfies the compatibility property `f.isCompat`.

`PolynomialLaw.toFun_eq_toFun'` proves that it extends `f.toFun'`.

-/

universe u v w

open scoped TensorProduct
open AlgHom LinearMap

section Lemmas

section fg

theorem Subalgebra.fg_sup {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]
    {A B : Subalgebra R S} (hA : A.FG) (hB : B.FG) : Subalgebra.FG (A ⊔ B) := by
  classical
  rw [← hA.choose_spec, ← hB.choose_spec, ← Algebra.adjoin_union, ← Finset.coe_union]
  exact ⟨hA.choose ∪ hB.choose, rfl⟩

end fg

section range

variable {R S T : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T)

theorem AlgHom.factor (φ : S →ₐ[R] T) :
    φ = φ.range.val.comp
      ((RingCon.quotientKerEquivRangeₐ φ).toAlgHom.comp
        ((RingCon.ker φ).mk'ₐ (S := R))) := by aesop

theorem AlgHom.comp_rangeRestrict :
    (Subalgebra.val _).comp φ.rangeRestrict = φ := by aesop

theorem RingCon.quotientKerEquivRangeₐ_mk :
    (RingCon.quotientKerEquivRangeₐ φ).toAlgHom.comp
      (RingCon.mk'ₐ R (RingCon.ker φ)) = φ.rangeRestrict := by
    aesop

theorem RingCon.kerLiftₐ_eq_val_comp_Equiv :
     RingCon.kerLiftₐ φ = (Subalgebra.val _).comp (RingCon.quotientKerEquivRangeₐ φ).toAlgHom :=
  AlgHom.ext fun _ ↦ refl _

theorem MvPolynomial.aeval_range (R : Type*) [CommSemiring R] (S : Type*) [CommSemiring S]
    [Algebra R S] {σ : Type*} (s : σ → S) :
    (aeval s).range = Algebra.adjoin R (Set.range s) := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | C a =>
      simp only [aeval_C, Algebra.mem_adjoin_iff]
      exact Subsemiring.subset_closure (Or.inl (Set.mem_range_self a))
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p n h =>
      simp only [map_mul, aeval_X]
      exact Subalgebra.mul_mem _ h (Algebra.subset_adjoin (Set.mem_range_self n))
  · rw [Algebra.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    use X i, by aesop

#find_home! MvPolynomial.aeval_range
theorem Subalgebra.val_comp_inclusion {R : Type*} [CommSemiring R] {S : Type*} [Semiring S]
    [Algebra R S] {A B : Subalgebra R S} (h : A ≤ B) :
  (Subalgebra.val B).comp (Subalgebra.inclusion h) = Subalgebra.val A := rfl

def Algebra.toAlgHom (R : Type*) [CommSemiring R]
    (S : Type*) [Semiring S] [Algebra R S] :
    R →ₐ[R] S where
  toRingHom := algebraMap R S
  commutes' := fun _ ↦ rfl

end range

section rTensor
theorem rTensor_comp_baseChange_comm_apply
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {S : Type*} [CommRing S] [Algebra R S]
    {S' : Type*} [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') (t : S ⊗[R] M) (f : M →ₗ[R] N) :
    (φ.toLinearMap.rTensor N) (f.baseChange S t)  =
      (f.baseChange S') (φ.toLinearMap.rTensor M t) := by
  simp [LinearMap.baseChange_eq_ltensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp]

end rTensor

theorem AlgEquiv.self_trans_symm_eq_refl
  {R S S' : Type*} [CommSemiring R] [Semiring S] [Semiring S']
  [Algebra R S] [Algebra R S'] (e : S ≃ₐ[R] S') :
  e.trans e.symm = AlgEquiv.refl := by aesop

theorem AlgEquiv.symm_trans_self_eq_refl
  {R S S' : Type*} [CommSemiring R] [Semiring S] [Semiring S']
  [Algebra R S] [Algebra R S'] (e : S ≃ₐ[R] S') :
  e.symm.trans e = AlgEquiv.refl := by
  aesop

end Lemmas

noncomputable section PolynomialLaw
open scoped TensorProduct

open MvPolynomial

variable (R : Type u) [CommSemiring R]
  (M : Type*) [AddCommMonoid M] [Module R M]
  (N : Type*) [AddCommMonoid N] [Module R N]

namespace PolynomialLaw

variable (f : M →ₚₗ[R] N)

section Lift

open LinearMap

variable (S : Type v) [CommSemiring S] [Algebra R S]

/-- The type of lifts of  `S ⊗[R] M` to a polynomial ring. -/
def lifts : Type _ := Σ (s : Finset S), (MvPolynomial (Fin s.card) R) ⊗[R] M

variable {M S}

/-- The lift of `f.toFun to the type `lifts` -/
private def φ (s : Finset S) : MvPolynomial (Fin s.card) R →ₐ[R] S :=
  MvPolynomial.aeval  (R := R) (fun n ↦ (s.equivFin.symm n : S))

private theorem φ_range (s : Finset S) : (φ R s).range = Algebra.adjoin R s := by
  simp only [φ]
  rw [aeval_range]
  congr
  rw [← Function.comp_def, Set.range_comp]
  simp only [Equiv.range_eq_univ, Set.image_univ, Subtype.range_coe_subtype, Finset.setOf_mem]

variable (M S) in
/-- The projection from `φ` to `S ⊗[R] M`. -/
private def π : lifts R M S → S ⊗[R] M := fun ⟨s, p⟩ ↦ rTensor M (φ R s).toLinearMap p

variable {R N}

def toFunLifted : lifts R M S → S ⊗[R] N :=
  fun ⟨s,p⟩ ↦ rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

variable (S)

/-- The extension of `PolynomialLaw.toFun'` to all universes. -/
def toFun : S ⊗[R] M → S ⊗[R] N := Function.extend (π R M S) (f.toFunLifted) (fun _ ↦ 0)

variable {S}

theorem Subalgebra.FG.exists_range_eq {B : Subalgebra R S} (hB : Subalgebra.FG B) :
    ∃ s : Finset S, (φ R s).range = B :=
  ⟨hB.choose, by simp only [φ_range, hB.choose_spec]⟩

--MI: I added this, but I am not sure whether it will be useful.
theorem toFun'_eq_of_diagram' {A : Type u} [CommSemiring A] [Algebra R A] {φ : A →ₐ[R] S} (p : A ⊗[R] M)
    {T : Type w} [CommSemiring T] [Algebra R T] {B : Type u} [CommSemiring B] [Algebra R B] {ψ : B →ₐ[R] T}
    (hψ : Function.Injective (LinearMap.rTensor (R := R) (N := B) (P := T) M ψ))
    (q : B ⊗[R] M) (g : A →ₐ[R] B) (h : S →ₐ[R] T) (hgh : ψ.comp g = h.comp φ)
    (hpq : (h.comp φ).toLinearMap.rTensor M p = ψ.toLinearMap.rTensor M q) :
    (h.comp φ).toLinearMap.rTensor N (f.toFun' A p) = ψ.toLinearMap.rTensor N (f.toFun' B q) := by
  rw [← hgh, comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.coe_comp, Function.comp_apply]
    at hpq ⊢
  rw [f.isCompat_apply', hψ hpq]

/-- Compare the values of `PolynomialLaw.toFun' in a square diagram -/
theorem toFun'_eq_of_diagram
    {A : Type u} [CommSemiring A] [Algebra R A]
    {φ : A →ₐ[R] S} (p : A ⊗[R] M)
    {T : Type w} [Semiring T] [Algebra R T]
    {B : Type u} [CommSemiring B] [Algebra R B]
    {ψ : B →ₐ[R] T} (q : B ⊗[R] M)
    (h : S →ₐ[R] T) (h' : φ.range →ₐ[R] ψ.range)
    (hh' : ψ.range.val.comp h' = h.comp φ.range.val)
    (hpq : (h'.comp φ.rangeRestrict).toLinearMap.rTensor M p =
      ψ.rangeRestrict.toLinearMap.rTensor M q) :
    (h.comp φ).toLinearMap.rTensor N (f.toFun' A p) =
      ψ.toLinearMap.rTensor N (f.toFun' B q) := by
  let θ := (RingCon.quotientKerEquivRangeₐ (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (RingCon.quotientKerEquivRangeₐ φ).toAlgHom)
  have ht : (h.comp φ.range.val).comp (RingCon.quotientKerEquivRangeₐ φ).toAlgHom =
      ψ.range.val.comp ((RingCon.quotientKerEquivRangeₐ ψ).toAlgHom.comp  θ) := by
    simp only [θ, ← AlgHom.comp_assoc, ← hh']
    simp [AlgHom.comp_assoc]
  rw [φ.factor, ψ.factor, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc _, ht]
  simp only [AlgHom.comp_toLinearMap, rTensor_comp_apply, LinearMap.comp_apply]
  apply congr_arg
  rw [← rTensor_comp_apply, ← AlgHom.comp_toLinearMap, isCompat_apply',
    isCompat_apply', AlgHom.comp_toLinearMap, rTensor_comp_apply,
    isCompat_apply']
  apply congr_arg
  simp only [θ, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, AlgHom.comp_assoc]
  rw [RingCon.quotientKerEquivRangeₐ_mk, comp_toLinearMap,
    rTensor_comp_apply, hpq, ← rTensor_comp_apply, ← comp_toLinearMap,
    ← RingCon.quotientKerEquivRangeₐ_mk ψ, ← AlgHom.comp_assoc]
  simp

/-- Compare the values of `PolynomialLaw.toFun' in a square diagram,
  when one of the maps is an algebra inclusion  -/
theorem toFun'_eq_of_inclusion
    {A : Type u} [CommSemiring A] [Algebra R A]
    {φ : A →ₐ[R] S}
    {B : Type u} [CommSemiring B] [Algebra R B]
    {ψ : B →ₐ[R] S}
    (p : A ⊗[R] M) (q : B ⊗[R] M)
    (h : φ.range ≤  ψ.range)
    (hpq : ((Subalgebra.inclusion h).comp
      φ.rangeRestrict).toLinearMap.rTensor M p = ψ.rangeRestrict.toLinearMap.rTensor M q) :
    φ.toLinearMap.rTensor N (f.toFun' A p) = ψ.toLinearMap.rTensor N (f.toFun' B q) :=
  toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq

theorem toFunLifted_factorsThrough_π :
    Function.FactorsThrough f.toFunLifted (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]
  set u := rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ (Algebra.FiniteType.mvPolynomial R (Fin s.card)).out
  set u' := rTensor M (φ R s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φ R s').range := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ (Algebra.FiniteType.mvPolynomial R (Fin s'.card)).out
  have huu' : rTensor M (Subalgebra.val _).toLinearMap u =
    rTensor M (Subalgebra.val _).toLinearMap u' := by
    simp only [π] at h
    simp only [hu, hu', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap,
      comp_rangeRestrict, h]
  obtain ⟨B, hAB, hA'B, ⟨t, hB⟩, h⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq' (R := R) uFG u u'FG u' huu'
  rw [← φ_range R t, eq_comm] at hB
  have hAB' : (φ R s).range ≤ (φ R t).range := le_trans hAB (le_of_eq hB)
  have hA'B' : (φ R s').range ≤ (φ R t).range := le_trans hA'B (le_of_eq hB)
  have : ∃ q : MvPolynomial (Fin t.card) R ⊗[R] M, rTensor M (toLinearMap (φ R t).rangeRestrict) q =
      rTensor M ((Subalgebra.inclusion (le_of_eq hB)).comp
        (Subalgebra.inclusion hAB)).toLinearMap u :=
    rTensor_surjective _ (rangeRestrict_surjective _) _
  obtain ⟨q, hq⟩ := this
  rw [toFun'_eq_of_inclusion f p q hAB', toFun'_eq_of_inclusion f p' q hA'B']
  · simp only [hq, comp_toLinearMap, rTensor_comp, LinearMap.comp_apply]
    rw [← hu', h]
    simp only [← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    rfl
  · simp only [hq, hu, ← LinearMap.comp_apply, comp_toLinearMap, rTensor_comp]
    congr; ext; rfl

theorem toFun_eq_toFunLifted_apply {t : S ⊗[R] M} {s : Finset S}
    {p : MvPolynomial (Fin s.card) R ⊗[R] M} (ha : π R M S (⟨s, p⟩ : lifts R M S) = t) :
    f.toFun S t = (φ R s).toLinearMap.rTensor N (f.toFun' _ p) := by
  rw [PolynomialLaw.toFun, ← ha, (toFunLifted_factorsThrough_π f).extend_apply, toFunLifted]

theorem exists_lift_of_le_rTensor_range
    {T : Type*} [CommSemiring T] [Algebra R T]
    (A : Subalgebra R T) {φ : S →ₐ[R] T} (hφ : A ≤ φ.range) {t : T ⊗[R] M}
    (ht : t ∈ range ((Subalgebra.val A).toLinearMap.rTensor M)) :
    ∃ s : S ⊗[R] M, φ.toLinearMap.rTensor M s = t := by
  obtain ⟨u, hu⟩ := ht
  suffices h_surj: Function.Surjective ((φ.rangeRestrict.toLinearMap).rTensor M) by
    obtain ⟨p, hp⟩ := h_surj ((Subalgebra.inclusion hφ).toLinearMap.rTensor M u)
    use p
    rw [← hu, ← Subalgebra.val_comp_inclusion hφ, comp_toLinearMap, rTensor_comp,
      LinearMap.comp_apply, ← hp, ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    rfl
  exact rTensor_surjective M (rangeRestrict_surjective φ)

/-- Tensor products in `S ⊗[R] M` can be lifted to some `MvPolynomial R n ⊗[R] M`, for a finite `n`-/
theorem π_surjective : Function.Surjective (π R M S) := by
  classical
  intro t
  obtain ⟨B : Subalgebra R S, hB : B.FG, ht : t ∈ range _⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨s : Finset S, hs : (PolynomialLaw.φ R s).range = B⟩ := Subalgebra.FG.exists_range_eq hB
  obtain ⟨p, hp⟩ := exists_lift_of_le_rTensor_range B (le_of_eq hs.symm) ht
  exact ⟨⟨s, p⟩, hp⟩

/-- Lift an element of a tensor product -/
theorem exists_lift (t : S ⊗[R] M) : ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (p : MvPolynomial (Fin n) R ⊗[R] M), ψ.toLinearMap.rTensor M p = t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

/-- Lift an element of a tensor product and a scalar -/
theorem exists_lift' (t : S ⊗[R] M) (s : S) : ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S)
    (p : MvPolynomial (Fin n) R ⊗[R] M) (q : MvPolynomial (Fin n) R),
      ψ.toLinearMap.rTensor M p = t ∧ ψ q = s := by
  classical
  obtain ⟨A, hA, ht⟩ := TensorProduct.Algebra.exists_of_fg t
  have hB : Subalgebra.FG (A ⊔ Algebra.adjoin R ({s} : Finset S)) :=
    Subalgebra.fg_sup hA (Subalgebra.fg_adjoin_finset _)
  obtain ⟨gen, hgen⟩ := Subalgebra.FG.exists_range_eq hB
  have hAB : A ≤ A ⊔ Algebra.adjoin R ({s} : Finset S) := le_sup_left
  rw [← hgen] at hAB
  obtain ⟨p, hp⟩ := exists_lift_of_le_rTensor_range _ hAB ht
  have hs : s ∈ (φ R gen).range  := by
    rw [hgen]
    apply Algebra.subset_adjoin
    simp only [Finset.coe_singleton, Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
    exact Or.inr (Algebra.subset_adjoin rfl)
  use gen.card, φ R gen, p, hs.choose, hp, hs.choose_spec

/-- For semirings in the universe `u`, `PolynomialLaw.toFun` coincides with `PolynomialLaw.toFun'` -/
theorem toFun_eq_toFun' (S : Type u) [CommSemiring S] [Algebra R S] :
    f.toFun S = f.toFun' S := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_toFunLifted_apply ha, toFunLifted, f.isCompat_apply']
  exact congr_arg _ ha

/-- For semirings in the universe `u`, `PolynomialLaw.toFun` coincides with `PolynomialLaw.toFun'` -/
theorem toFun_eq_toFun'_apply (S : Type u) [CommSemiring S] [Algebra R S] (t : S ⊗[R] M) :
    f.toFun S t = f.toFun' S t := congr_fun (f.toFun_eq_toFun' S) t

/-- Extends `PolynomialLaw.isCompat_apply'` to all universes. -/
theorem isCompat_apply {T : Type w} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T) (t : S ⊗[R] M) :
    rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTensor M h.toLinearMap t) := by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h
  let h' : (φ R s).range →ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [φ_range] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, Finset.coe_image,
      Algebra.adjoin_image, s']
    exact ⟨x, hx, rfl⟩)
  let j : Fin s.card → Fin s'.card :=
    (s'.equivFin) ∘ (fun ⟨x, hx⟩ ↦ ⟨h x, Finset.mem_image_of_mem h hx⟩) ∘ (s.equivFin).symm
  have eq_h_comp : (φ R s').comp (rename j) = h.comp (φ R s) := by
    ext p
    simp only [φ, AlgHom.comp_apply, aeval_rename, comp_aeval]
    congr
    ext n
    simp only [Function.comp_apply, Equiv.symm_apply_apply, j]
  let p' := rTensor M (rename j).toLinearMap  p
  have ha' : π R M T (⟨s', p'⟩ : lifts R M T) = rTensor M h.toLinearMap t := by
    simp only [← ha, π, p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap, eq_h_comp]
  rw [toFun_eq_toFunLifted_apply f ha, toFun_eq_toFunLifted_apply f ha', ← LinearMap.comp_apply,
    ← rTensor_comp, ← comp_toLinearMap]
  apply toFun'_eq_of_diagram f p p' h h'
  · simp only [val_comp_codRestrict, AlgHom.coe_comp, Subalgebra.coe_val,Function.comp_apply, h']
  · simp only [p', ← LinearMap.comp_apply, ← rTensor_comp, ← comp_toLinearMap]
    congr
    ext n
    simp only [AlgHom.coe_comp, Function.comp_apply, coe_codRestrict,
      Subalgebra.coe_val, rename_X, h', j]
    simp only [φ, aeval_X, Equiv.symm_apply_apply]

/-- Extends `PolynomialLaw.isCompat` to all universes -/
theorem isCompat {T : Type w} [CommSemiring T] [Algebra R T] (h : S →ₐ[R] T) :
    h.toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M := by
  ext t
  simp only [Function.comp_apply, PolynomialLaw.isCompat_apply]

end Lift

section Module

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N] (r a b : R) (f g : M →ₚₗ[R] N)

/-- Extension of `PolynomialLaw.zero_def` -/
theorem zero_toFun (S : Type*) [CommSemiring S] [Algebra R S] :
    (0 : M →ₚₗ[R] N).toFun S = 0 := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_toFunLifted_apply _ ha, zero_def, Pi.zero_apply, _root_.map_zero]

/-- Extension of `PolynomialLaw.add_def_apply` -/
theorem add_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] (t : S ⊗[R] M) :
    (f + g).toFun S t = f.toFun S t + g.toFun S t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_toFunLifted_apply _ ha, add_def, map_add]

/-- Extension of `PolynomialLaw.add_def` -/
theorem add_toFun {S : Type*} [CommSemiring S] [Algebra R S] :
    (f + g).toFun S = f.toFun S + g.toFun S := by
  ext t
  simp only [Pi.add_apply, add_toFun_apply]

theorem neg_toFun {R : Type u} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] :
    (-f).toFun S = (-1 : R) • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp [toFun_eq_toFunLifted_apply _ ha, neg_def]

/-- Extension of `PolynomialLaw.smul_def` -/
theorem smul_toFun (S : Type*) [CommSemiring S] [Algebra R S] :
    (r • f).toFun S = r • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_toFunLifted_apply _ ha, smul_def, Pi.smul_apply, map_smul]

end Module

section ground

variable {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₚₗ[R] N)

theorem isCompat_apply'_ground {S : Type u} [CommSemiring S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun' S) (1 ⊗ₜ x) := by
  simp only [ground]
  convert f.isCompat_apply' (Algebra.toAlgHom R S) (1 ⊗ₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, map_one]

theorem isCompat_apply_ground (S : Type*) [CommSemiring S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun S) (1 ⊗ₜ x) := by
  simp only [ground, ← toFun_eq_toFun']
  convert f.isCompat_apply (Algebra.toAlgHom R S) (1 ⊗ₜ[R] x)
  · simp only [Function.comp_apply, TensorProduct.lid_symm_apply, TensorProduct.includeRight_lid]
    congr
  · rw [rTensor_tmul, toLinearMap_apply, _root_.map_one]

end ground

section Comp

variable {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  {P : Type*} [AddCommMonoid P] [Module R P]
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  (f : M →ₚₗ[R] N) (g : N →ₚₗ[R] P) (h : P →ₚₗ[R] Q)

/-- Extension of `MvPolynomial.comp_toFun'` -/
theorem comp_toFun (S : Type*) [CommSemiring S] [Algebra R S] :
    (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialLaw.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_toFunLifted_apply _ ha, π]
  rw [Function.comp_apply, toFun_eq_toFunLifted_apply _ hb, toFun_eq_toFunLifted_apply _ ha,
    comp_toFun', Function.comp_apply]

theorem comp_apply (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    (g.comp f).toFun S m = (g.toFun S) (f.toFun S m) := by
  simp only [comp_toFun, Function.comp_apply]

end Comp
