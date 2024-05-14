/- Copyright ACL @ MIdFF 2024 -/

import DividedPowers.ForMathlib.RingTheory.TensorProduct.Polynomial
import DividedPowers.ForMathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

import DividedPowers.ForMathlib.DirectLimit
import DividedPowers.ForMathlib.RingTheory.SubmoduleMem

/-! # Polynomial laws on modules

Let `M` and `N` be a modules over a commutative ring `R`.
A polynomial map `f : PolynomialMap R M N`, with notation `f : M →ₚ[R] N`,
is a “law” that assigns, to every `R`-algebra `S`,
* a map `PolynomialMap.toFun' f S : S ⊗[R] M → S ⊗[R] N`,
* compatibly with morphisms of `R`-algebras, as expressed by `PolynomialMap.isCompat' f`

For type theoretic reasons, if `R : Type u`,
then the definition of the polynomial map `f`
is restricted to `R`-algebras `S` such that `S : Type u`.
Using the fact that a module is the direct limit
of its finitely generated submodules,
that a finitely generated subalgebra is a quotient
of a polynomial ring in the universe `u`,
plus commutation of tensor products with direct limits,
we extend the functor to all `R`-algebras.

* `PolynomialMap.toFun` is the universal extension of `PolynomialMap.toFun'`
* `PolynomialMap.isCompat` is the universal extension of `PolynomialMap.isCompat'`

* `PolynomialMap.instModule : Module R (M →ₚ[R] N)`
  shows that polynomial maps form a `R`-module.

* `PolynomialMap.ground f`  is the map `M → N` corresponding to `PolynomialMap.toFun' f R` under the isomorphisms `R ⊗[R] M ≃ₗ[R] M`, and similarly for `N`.

In further files, we construct the coefficients of a polynomial map,
and show the relation with polynomials (when the module `M` is free and finite).

Reference : Roby, Norbert. 1963. « Lois polynomes et lois formelles en théorie des modules ». Annales scientifiques de l’École Normale Supérieure 80 (3): 213‑348. https://doi.org/10.24033/asens.1124.

## Construction of the universal extension

The idea of the universal extension is standard,
setting it up in detail is sometimes technical.

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

## Extension to commutative semirings

Mathematically, the theory could only assume that `R` is a commutative semiring,
and `M`, `N` are `AddCommMonoid`.
However, the present state of direct limits in mathlib
uses quotients by submodules (rather than by adequate equivalence relations),
so that, for the moment, the theory imposes that we have `CommRing R`
and `AddCommGroup M`, `AddCommGroup N`.

-/

universe u v w

open scoped TensorProduct
open LinearMap

section Lemmas

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

theorem AlgHom.factor
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [Semiring T] [Algebra R T] (φ : S →ₐ[R] T) :
    φ = φ.range.val.comp
        ((Ideal.quotientKerEquivRange φ).toAlgHom.comp
          (Ideal.Quotient.mkₐ R (RingHom.ker φ))) := by ext; rfl

theorem AlgHom.comp_rangeRestrict
    {R : Type*} [CommSemiring R]
    {S : Type*} [Semiring S] [Algebra R S]
    {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T) :
    (Subalgebra.val _).comp φ.rangeRestrict = φ := by
  ext; rfl

theorem AlgHom.quotientKerEquivRange_mk
    {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T)  :
    (Ideal.quotientKerEquivRange φ).toAlgHom.comp
      (Ideal.Quotient.mkₐ R (RingHom.ker φ)) = φ.rangeRestrict := by
  ext s
  simp only [AlgEquiv.toAlgHom_eq_coe, coe_comp, AlgHom.coe_coe,
    Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, coe_codRestrict]
  rfl

theorem Ideal.kerLiftAlg_eq_val_comp_Equiv
    {R : Type*} [CommRing R]
    {S : Type*} [CommRing S] [Algebra R S]
    {T : Type*} [Semiring T] [Algebra R T]
    (φ : S →ₐ[R] T) :
    Ideal.kerLiftAlg φ
      = (Subalgebra.val _).comp (Ideal.quotientKerEquivRange φ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  ext s; simp; rfl

theorem MvPolynomial.aeval_range
    (R : Type*) [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    {σ : Type*} (s : σ → S) :
    (aeval (R := R) s).range = Algebra.adjoin R (Set.range s) := by
  apply le_antisymm
  · intro x
    rintro ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | h_C a =>
      simp only [aeval_C, Algebra.mem_adjoin_iff]
      apply Subsemiring.subset_closure
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

theorem Subalgebra.val_comp_inclusion {R : Type*} [CommSemiring R]
    {S : Type*} [Semiring S] [Algebra R S]
    {A B : Subalgebra R S} (h : A ≤ B) :
  (Subalgebra.val B).comp (Subalgebra.inclusion h) = Subalgebra.val A := rfl

def algebraMap' (R : Type*) [CommSemiring R]
    (S : Type*) [Semiring S] [Algebra R S] :
    R →ₐ[R] S where
  toRingHom := algebraMap R S
  commutes' := fun _ ↦ rfl

lemma TensorProduct.includeRight_lid
    {R  : Type*} [CommSemiring R]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {M : Type*} [AddCommMonoid M] [Module R M] (m) :
    (1 : S)  ⊗ₜ[R] (TensorProduct.lid R M) m =
      (rTensor M (algebraMap' R S).toLinearMap) m := by
  suffices ∀ m, (rTensor M (algebraMap' R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 ⊗ₜ[R] m by
    simp [← this]
  intro z
  simp


end Lemmas

noncomputable section PolynomialMap

open scoped TensorProduct

open MvPolynomial

variable (R : Type u) [CommRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (N : Type*) [AddCommGroup N] [Module R N]

 /-- A polynomial map `M →ₚ[R] N` between `R`-modules
  is a functorial family of maps `S ⊗[R] M → S ⊗[R] N`,
  for all `R`-algebras `S` -/
@[ext]
structure PolynomialMap  where
  toFun' (S : Type u) [CommRing S] [Algebra R S] : S ⊗[R] M → S ⊗[R] N
  isCompat' {S : Type u} [CommRing S] [Algebra R S]
    {S' : Type u} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') :
    φ.toLinearMap.rTensor N ∘ toFun' S = toFun' S' ∘ φ.toLinearMap.rTensor M
#align polynomial_map PolynomialMap

/-- `M →ₚ[R] N` is the type of `R`-polynomial maps from `M` to `N`. -/
notation:25 M " →ₚ[" R:25 "] " N:0 => PolynomialMap R M N

namespace PolynomialMap

variable (f : PolynomialMap R M N)

theorem isCompat_apply'
    {S : Type u} [CommRing S] [Algebra R S]
    {S' : Type u} [CommRing S'] [Algebra R S']
    (φ : S →ₐ[R] S') (x : S ⊗[R] M) :
  (φ.toLinearMap.rTensor N) ((f.toFun' S) x) =
      (f.toFun' S') (φ.toLinearMap.rTensor M x) := by
  simpa only using _root_.congr_fun (f.isCompat' φ) x
#align polynomial_map.is_compat_apply PolynomialMap.isCompat_apply'

section Lift

open LinearMap

variable (f : M →ₚ[R] N)

variable (S : Type v) [CommRing S] [Algebra R S]
/-- The type of lifts of  `S ⊗[R] M` to a polynomial ring -/
def lifts : Type _ := Σ (s : Finset S), (MvPolynomial (Fin s.card) R) ⊗[R] M


variable {M S}
/-- The lift of `f.toFun to the type `lifts` -/
private
noncomputable def φ (s : Finset S) :
    MvPolynomial (Fin s.card) R →ₐ[R] S :=
  MvPolynomial.aeval  (R := R) (fun n ↦ (s.equivFin.symm n : S))


private
theorem φ_range (s : Finset S) : (φ R s).range = Algebra.adjoin R s := by
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
      simp [φ]
  · rw [Algebra.adjoin_le_iff]
    intro x
    simp only [Finset.mem_coe, φ, AlgHom.coe_range, Set.mem_range]
    intro hx
    use X (s.equivFin ⟨x, hx⟩)
    simp

variable (M S)
/-- The projection from `φ` to `S ⊗[R] M` -/
private
noncomputable def π : lifts R M S → S ⊗[R] M :=
  fun ⟨s, p⟩ ↦ rTensor M (φ R s).toLinearMap p

variable {R M N S}

private
noncomputable def toFunLifted :
    lifts R M S → S ⊗[R] N := fun ⟨s,p⟩ ↦
  LinearMap.rTensor N (φ R s).toLinearMap (f.toFun' (MvPolynomial (Fin s.card) R) p)

variable (S)

/-- The extension of `PolynomialMap.toFun'` to all universes -/
noncomputable def toFun : S ⊗[R] M → S ⊗[R] N :=
  Function.extend (π R M S) (f.toFunLifted) (fun _ ↦ 0)

variable {S}
theorem Subalgebra.FG.exists_range_eq
    {B : Subalgebra R S} (hB : Subalgebra.FG B) :
    ∃ s : Finset S, (φ R s).range = B := by
  choose s hs using hB
  use s
  simp only [φ_range, hs]

/-- Compare the values of `PolynomialMap.toFun' in a square diagram -/
theorem toFun'_eq_of_diagram
    {A : Type u} [CommRing A] [Algebra R A] {φ : A →ₐ[R] S} (p : A ⊗[R] M)
    {T : Type w} [CommRing T] [Algebra R T]
    {B : Type u} [CommRing B] [Algebra R B] {ψ : B →ₐ[R] T } (q : B ⊗[R] M)
    (h : S →ₐ[R] T) (h' : φ.range →ₐ[R] ψ.range)
    (hh' : ψ.range.val.comp h' = h.comp φ.range.val)
    (hpq : (h'.comp φ.rangeRestrict).toLinearMap.rTensor M p
      = ψ.rangeRestrict.toLinearMap.rTensor M q) :
    (h.comp φ).toLinearMap.rTensor N (f.toFun' A p) =
      ψ.toLinearMap.rTensor N (f.toFun' B q) := by
  let θ := (Ideal.quotientKerEquivRange (R := R) ψ).symm.toAlgHom.comp
    (h'.comp (Ideal.quotientKerEquivRange φ).toAlgHom)
  have ht : h.comp (φ.range.val.comp (Ideal.quotientKerEquivRange φ).toAlgHom) =
      ψ.range.val.comp ((Ideal.quotientKerEquivRange ψ).toAlgHom.comp θ) := by
    simp only [θ]
    simp only [← AlgHom.comp_assoc, ← hh']
    apply congr_arg₂ _ _ rfl
    apply congr_arg₂ _ _ rfl
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_assoc, AlgEquiv.comp_symm, AlgHom.comp_id]
  simp only [φ.factor, ψ.factor, ← AlgHom.comp_assoc]
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

/-- Compare the values of `PolynomialMap.toFun' in a square diagram,
  when one of the maps is an algebra inclusion  -/
theorem toFun'_eq_of_inclusion
    {A : Type u} [CommRing A] [Algebra R A] {φ : A →ₐ[R] S} (p : A ⊗[R] M)
    {B : Type u} [CommRing B] [Algebra R B] {ψ : B →ₐ[R] S} (q : B ⊗[R] M)
    (h : φ.range ≤  ψ.range)
    (hpq : ((Subalgebra.inclusion h).comp φ.rangeRestrict).toLinearMap.rTensor M p = ψ.rangeRestrict.toLinearMap.rTensor M q) :
    φ.toLinearMap.rTensor N (f.toFun' A p) = ψ.toLinearMap.rTensor N (f.toFun' B q) :=
  toFun'_eq_of_diagram f p q (AlgHom.id R S) (Subalgebra.inclusion h) (by ext x; simp) hpq

theorem toFunLifted_factorsThrough_π :
    Function.FactorsThrough f.toFunLifted (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [toFunLifted]

  classical
  set u := LinearMap.rTensor M (φ R s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φ R s).range := by
    rw [← Algebra.map_top]
    apply Subalgebra.FG.map
    exact (Algebra.FiniteType.mvPolynomial R (Fin s.card)).out

  set u' := LinearMap.rTensor M (φ R s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φ R s').range := by
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
  rw [← φ_range R t, eq_comm] at hB
  have hAB' : (φ R s).range ≤ (φ R t).range := le_trans hAB (le_of_eq hB)
  have hA'B' : (φ R s').range ≤ (φ R t).range := le_trans hA'B (le_of_eq hB)
  have : ∃ q : MvPolynomial (Fin t.card) R ⊗[R] M,
    LinearMap.rTensor M (AlgHom.toLinearMap (φ R t).rangeRestrict) q
      = LinearMap.rTensor M ((Subalgebra.inclusion (le_of_eq hB)).comp (Subalgebra.inclusion hAB)).toLinearMap u := by
    suffices Function.Surjective (?_) by
      exact this _
    apply rTensor_surjective
    exact AlgHom.rangeRestrict_surjective _

  obtain ⟨q, hq⟩ := this
  rw  [toFun'_eq_of_inclusion f p q hAB', toFun'_eq_of_inclusion f p' q hA'B']
  · rw [hq]
    simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [← hu', h]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    congr
  · rw [hq, hu]
    simp only [← LinearMap.comp_apply, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp]
    congr; ext; rfl

theorem toFun_eq_toFunLifted_apply
    {t : S ⊗[R] M} {s : Finset S} {p : MvPolynomial (Fin s.card) R ⊗[R] M} (ha : π R M S (⟨s, p⟩ : lifts R M S) = t)  :
    f.toFun S t = (φ R s).toLinearMap.rTensor N (f.toFun' _ p) := by
  rw [PolynomialMap.toFun, ← ha, (toFunLifted_factorsThrough_π f).extend_apply,
    toFunLifted]

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
  exact LinearMap.rTensor_surjective M (by exact AlgHom.rangeRestrict_surjective φ)

/-- Tensor products in `S ⊗[R] M` can be lifted to some `MvPolynomial R n ⊗[R] M`, for a finite `n`-/
theorem π_surjective : Function.Surjective (π R M S) := by
  intro t
  choose B hB ht using TensorProduct.Algebra.exists_of_fg t
  choose s hs using Subalgebra.FG.exists_range_eq hB
  choose p hp using
    exists_lift_of_le_rTensor_range M B (le_of_eq hs.symm) t ht
  exact ⟨⟨s, p⟩, hp⟩

/-- Lift an element of a tensor product -/
theorem exists_lift (t : S ⊗[R] M) :
    ∃ (n : ℕ) (ψ : MvPolynomial (Fin n) R →ₐ[R] S) (p : MvPolynomial (Fin n) R ⊗[R] M),
      ψ.toLinearMap.rTensor M p = t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  use s.card, φ R s, p, ha

/-- Lift an element of a tensor product and a scalar -/
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
  have : s ∈ AlgHom.range (φ R gen) := by
    rw [hgen]
    apply Algebra.subset_adjoin
    simp only [Finset.coe_singleton, Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
    right
    exact Algebra.subset_adjoin rfl
  choose q hq using this
  use gen.card, φ R gen, p, q, hp, hq


/-- For rings in the universe `u`, `PolynomialMap.toFun` coincides with `PolynomialMap.toFun'` -/
theorem toFun_eq_toFun' (S : Type u) [CommRing S] [Algebra R S] :
    f.toFun S = f.toFun' S := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [f.toFun_eq_toFunLifted_apply ha, toFunLifted, f.isCompat_apply']
  apply congr_arg
  exact ha

/-- For rings in the universe `u`, `PolynomialMap.toFun` coincides with `PolynomialMap.toFun'` -/
theorem toFun_eq_toFun'_apply (S : Type u) [CommRing S] [Algebra R S] (t : S ⊗[R] M):
    f.toFun S t = f.toFun' S t :=
  congr_fun (f.toFun_eq_toFun' S) t

/-- Extends `PolynomialMap.isCompat_apply` to all universes -/
theorem isCompat_apply
    {T : Type w} [CommRing T] [Algebra R T] (h : S →ₐ[R] T) (t : S ⊗[R] M) :
    rTensor N h.toLinearMap (f.toFun S t) = f.toFun T (rTensor M h.toLinearMap t) := by
  classical
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  let s' := s.image h

  let h' : (φ R s).range →ₐ[R] (φ R s').range :=
    (h.comp (Subalgebra.val _)).codRestrict (φ R s').range (by
    rintro ⟨x, hx⟩
    simp only [φ_range] at hx ⊢
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply]
    simp only [Finset.coe_image, Algebra.adjoin_image, s']
    exact ⟨x, hx, rfl⟩)

  let j : Fin s.card → Fin s'.card :=
    (s'.equivFin) ∘ (fun ⟨x, hx⟩ ↦ ⟨h x, Finset.mem_image_of_mem h hx⟩) ∘ (s.equivFin).symm
  have eq_h_comp : (φ R s').comp (rename j) = h.comp (φ R s) := by
    ext p
    simp only [φ, AlgHom.comp_apply, aeval_rename, comp_aeval]
    congr
    ext n
    simp [j]

  let p' := rTensor M (rename j).toLinearMap  p
  have ha' : π R M T (⟨s', p'⟩ : lifts R M T) = rTensor M h.toLinearMap t := by
    simp only [← ha, π, p']
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    rw [eq_h_comp]

  rw [PolynomialMap.toFun_eq_toFunLifted_apply f ha]
  rw [PolynomialMap.toFun_eq_toFunLifted_apply f ha']
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
  apply toFun'_eq_of_diagram f p p' h h'
  · ext x; simp [h']
  · simp only [p']
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    apply LinearMap.congr_fun
    apply congr_arg
    apply congr_arg
    ext n
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_codRestrict,
      Subalgebra.coe_val, rename_X, h', j]
    simp only [φ, aeval_X, Equiv.symm_apply_apply]

/-- Extends `PolynomialMap.isCompat` to all universes -/
theorem isCompat
    {T : Type w} [CommRing T] [Algebra R T] (h : S →ₐ[R] T) :
    h.toLinearMap.rTensor N ∘ f.toFun S = f.toFun T ∘ h.toLinearMap.rTensor M := by
  ext t
  simp only [Function.comp_apply, PolynomialMap.isCompat_apply]

end Lift

section Module
variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
variable (r a b : R)
variable (f g : M →ₚ[R] N)

instance : Zero (M →ₚ[R] N) :=
  ⟨{  toFun' := fun _ => 0
      isCompat' := fun _ => rfl }⟩

@[simp]
theorem zero_def (S : Type u) [CommRing S] [Algebra R S] :
    (0 : PolynomialMap R M N).toFun' S = 0 :=
  rfl
#align polynomial_map.zero_def PolynomialMap.zero_def

instance : Inhabited (PolynomialMap R M N) :=
  ⟨Zero.zero⟩

/-- Extension of `MvPolynomial.zero_def` -/
theorem zero_toFun (S : Type*) [CommRing S] [Algebra R S] :
    (0 : M →ₚ[R] N).toFun S = 0 := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_toFunLifted_apply _ ha, zero_def, Pi.zero_apply, map_zero]

noncomputable def add : M →ₚ[R] N
    where
  toFun' S _ _ := f.toFun' S + g.toFun' S
  isCompat' φ := by
    ext
    simp only [Function.comp_apply, Pi.add_apply, map_add]
    simp only [Function.comp_apply, Pi.add_apply, map_add, isCompat_apply']
#align polynomial_map.add PolynomialMap.add

instance : Add (PolynomialMap R M N) :=
  ⟨add⟩

@[simp]
theorem add_def (S : Type u) [CommRing S] [Algebra R S] :
  (f + g).toFun' S = f.toFun' S + g.toFun' S := rfl

@[simp]
theorem add_def_apply (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
  (f + g).toFun' S m = f.toFun' S m + g.toFun' S m := rfl
#align polynomial_map.add_def_apply PolynomialMap.add_def_apply

/-- Extension of `MvPolynomial.add_def_apply` -/
theorem add_toFun_apply {S : Type*} [CommRing S] [Algebra R S] (t : S ⊗[R] M) :
    (f + g).toFun S t = f.toFun S t + g.toFun S t := by
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [Pi.add_apply, toFun_eq_toFunLifted_apply _ ha, add_def, map_add]

/-- Extension of `MvPolynomial.add_def` -/
theorem add_toFun {S : Type*} [CommRing S] [Algebra R S] :
    (f + g).toFun S = f.toFun S + g.toFun S := by
  ext t
  simp only [Pi.add_apply, add_toFun_apply]

noncomputable def neg : M →ₚ[R] N where
  toFun' S _ _ := - f.toFun' S
  isCompat' φ := by
    ext t
    simp [isCompat_apply']

instance : Neg (M →ₚ[R] N) where
  neg := neg

@[simp]
theorem neg_def (S : Type u) [CommRing S] [Algebra R S] :
    (-f).toFun' S = - f.toFun' S := rfl

/-- External multiplication of a `f : M →ₚ[R] N` by `r : R` -/
def smul : M →ₚ[R] N where
  toFun' S _ _ := r • f.toFun' S
  isCompat' φ := by
    ext m
    simp only [Function.comp_apply, Pi.smul_apply, map_smul, isCompat_apply']
#align polynomial_map.smul PolynomialMap.smul

instance hasSmul : SMul R (PolynomialMap R M N) :=
  ⟨smul⟩
#align polynomial_map.has_smul PolynomialMap.hasSmul

@[simp]
theorem smul_def (S : Type u) [CommRing S] [Algebra R S] :
    (r • f).toFun' S = r • f.toFun' S :=
  rfl
#align polynomial_map.smul_def PolynomialMap.smul_def

@[simp]
theorem smul_def_apply (S : Type u) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (r • f).toFun' S m = r • f.toFun' S m :=
  rfl

/-- Extension of `MvPolynomial.smul_def` -/
theorem smul_toFun (S : Type*) [CommRing S] [Algebra R S] :
    (r • f).toFun S = r • (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  simp only [toFun_eq_toFunLifted_apply _ ha, smul_def, Pi.smul_apply, map_smul]

theorem add_smul : (a + b) • f = a • f + b • f := by
  ext S _ _ x
  simp only [add_def, smul_def, _root_.add_smul]

@[simp]
theorem zero_smul : (0 : R) • f = 0 := by
  ext S _ _ x
  simp only [smul_def, _root_.zero_smul, zero_def, Pi.zero_apply]

@[simp]
theorem one_smul : (1 : R) • f = f := by
  ext S _ _ x
  simp only [smul_def, Pi.smul_apply, _root_.one_smul]

instance : MulAction R (M →ₚ[R] N) where
  one_smul f := by ext; simp only [smul_def, one_smul]
  mul_smul a b f := by ext; simp only [smul_def, mul_smul]

instance addCommGroup : AddCommGroup (M →ₚ[R] N) where
  add_assoc f g h := by ext; simp only [add_def, add_assoc]
  zero_add f := by ext; simp only [add_def, zero_add, zero_def]
  add_zero f := by ext; simp only [add_def, add_zero, zero_def]
  nsmul n f := (n : R) • f
  nsmul_zero f := by simp only [Nat.cast_zero, zero_smul f]
  nsmul_succ n f := by
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  zsmul n f := (n : R) • f
  zsmul_zero' f := by
    simp only [Int.cast_zero, zero_smul]
  zsmul_succ' n f := by
    simp only [Int.ofNat_eq_coe, Nat.cast_succ, Int.cast_add, Int.cast_natCast,
      Int.cast_one, add_smul, _root_.one_smul]
  zsmul_neg' n f := by
    ext
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev,
      smul_def_apply, _root_.add_smul, neg_smul, _root_.one_smul,
      Nat.cast_succ, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_def,
      smul_def, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]
  add_left_neg f := by
    ext
    simp only [add_def_apply, neg_def, Pi.neg_apply, add_left_neg, zero_def, Pi.zero_apply]
  add_comm f g := by ext; simp only [add_def, add_comm]
#align polynomial_map.add_comm_monoid PolynomialMap.addCommGroup

instance instModule : Module R (M →ₚ[R] N) where
  smul_zero a := rfl
  smul_add a f g := by ext; simp only [smul_def, add_def, smul_add]
  add_smul := add_smul
  zero_smul := zero_smul
#align polynomial_map.module PolynomialMap.instModule

end Module

section ground

variable {R : Type u} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
variable (f : M →ₚ[R] N)
/-- The map `M → N` associated with a `f : M →ₚ[R] N` (essentially, `f.toFun' R`) -/
def ground : M → N :=
  (TensorProduct.lid R N) ∘ (f.toFun' R) ∘ (TensorProduct.lid R M).symm

theorem isCompat_apply'_ground {S : Type u} [CommRing S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun' S) (1 ⊗ₜ x) := by
  simp only [ground]
  convert f.isCompat_apply' (algebraMap' R S) (1 ⊗ₜ[R] x)
  simp only [Function.comp_apply, TensorProduct.lid_symm_apply]
  rw [TensorProduct.includeRight_lid]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

theorem isCompat_apply_ground (S : Type*) [CommRing S] [Algebra R S] (x : M) :
    1 ⊗ₜ (f.ground x) = (f.toFun S) (1 ⊗ₜ x) := by
  simp only [ground, ← toFun_eq_toFun']
  convert f.isCompat_apply (algebraMap' R S) (1 ⊗ₜ[R] x)
  simp only [Function.comp_apply, TensorProduct.lid_symm_apply]
  rw [TensorProduct.includeRight_lid]
  simp only [rTensor_tmul, AlgHom.toLinearMap_apply, _root_.map_one]

def lground : (M →ₚ[R] N) →ₗ[R] (M → N) where
  toFun := ground
  map_add' x y := by
    ext m; simp [ground]
  map_smul' r x := by
    ext m; simp [ground]

end ground
section Comp

variable {R : Type u} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {P : Type*} [AddCommGroup P] [Module R P]
variable {Q : Type*} [AddCommGroup Q] [Module R Q]
variable (f : PolynomialMap R M N) (g : PolynomialMap R N P) (h : PolynomialMap R P Q)

def comp (g : PolynomialMap R N P) (f : PolynomialMap R M N) : PolynomialMap R M P where
  toFun' S _ _ := (g.toFun' S).comp (f.toFun' S)
  isCompat' φ := by ext; simp only [Function.comp_apply, isCompat_apply']
#align polynomial_map.comp PolynomialMap.comp

theorem comp_toFun' (S : Type u) [CommRing S] [Algebra R S] :
  (g.comp f).toFun' S = (g.toFun' S).comp (f.toFun' S) := rfl
#align polynomial_map.comp_to_fun PolynomialMap.comp_toFun'

/-- Extension of `MvPolynomial.comp_toFun'` -/
theorem comp_toFun (S : Type*) [CommRing S] [Algebra R S] :
    (g.comp f).toFun S = (g.toFun S).comp (f.toFun S) := by
  ext t
  obtain ⟨⟨s, p⟩, ha⟩ := π_surjective t
  have hb : PolynomialMap.π R N S ⟨s, f.toFun' _ p⟩ = f.toFun S t := by
    simp only [toFun_eq_toFunLifted_apply _ ha, π]
  simp only [Function.comp_apply]
  simp only [toFun_eq_toFunLifted_apply _ hb]
  simp only [toFun_eq_toFunLifted_apply _ ha, comp_toFun', Function.comp_apply]

theorem comp_apply (S : Type*) [CommRing S] [Algebra R S] (m : S ⊗[R] M) :
    (g.comp f).toFun S m = (g.toFun S) (f.toFun S m) := by
  simp only [comp_toFun, Function.comp_apply]
#align polynomial_map.comp_apply PolynomialMap.comp_apply

theorem comp_assoc :
  h.comp (g.comp f) = (h.comp g).comp f := by
  ext; simp only [comp_toFun'] ; rfl
#align polynomial_map.comp_assoc PolynomialMap.comp_assoc

end Comp
