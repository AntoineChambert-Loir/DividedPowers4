import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic

def Subalgebra.subtype {R S : Type} [CommSemiring R] [Semiring S] [Algebra R S] (A : Subalgebra R S) : A →ₐ[R] S := by
  exact val A

namespace AlgHom

variable {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : Type w} [Ring T] [Algebra R T]
    {T' : Type w} [Semiring T'] [Algebra R T']

/-- The **first isomorphism theorem** for commutative algebras, surjective case. -/
noncomputable example {f : S →ₐ[R] T} (hf : Function.Surjective f) :
    (S ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] T  :=
  Ideal.quotientKerAlgEquivOfSurjective hf

theorem ker_rangeRestrict (f : S →ₐ[R] T) :
    RingHom.ker f.rangeRestrict = RingHom.ker f :=
  RingHom.ker_rangeRestrict f.toRingHom

theorem rangeRestrict_surjective (f : S →ₐ[R] T):
    Function.Surjective (f.rangeRestrict) :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := hy
  ⟨x, SetCoe.ext hx⟩

theorem range_top_iff_surjective {f : S →ₐ[R] T} :
    f.range = (⊤ : Subalgebra R T) ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, Algebra.coe_top]) Set.range_iff_surjective

theorem range_top_of_surjective (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.range = ⊤ :=
  range_top_iff_surjective.2 hf

example (f : S →+* T) (hf : Function.Surjective f) :
    f.range ≃+* T :=
  (RingHom.range_top_of_surjective f hf) ▸ Subring.topEquiv

example (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    f.range ≃ₐ[R] T :=
  (range_top_of_surjective f hf) ▸ Subalgebra.topEquiv

/-- The **first isomorphism theorem** for commutative algebras (`AlgHom.range` version). -/
noncomputable def quotientKerEquivRange (f : S →ₐ[R] T) :
  (S ⧸ RingHom.ker f) ≃ₐ[R] f.range :=
  (Ideal.quotientEquivAlgOfEq R f.ker_rangeRestrict.symm).trans <|
-- it necessary to add `(f := …)` here, otherwise Lean times out…
    Ideal.quotientKerAlgEquivOfSurjective (f := f.rangeRestrict)
      f.rangeRestrict_surjective

def rangeS (f : S →ₐ[R] T') : Subalgebra R T' :=
{ f.toRingHom.rangeS with
  algebraMap_mem' := fun r => ⟨algebraMap R S r, f.commutes r⟩ }

theorem mem_rangeS {f : S →ₐ[R] T'} {y : T'} :
    y ∈ f.rangeS ↔ ∃ x, f x = y :=
  { mp := fun a => a, mpr := fun a => a }

def rangeSRestrict (f : S →ₐ[R] T') : S →ₐ[R] f.rangeS :=
  AlgHom.codRestrict f f.rangeS (fun x ↦ ⟨x, rfl⟩)

theorem ker_rangeSRestrict (f : S →ₐ[R] T') :
    RingHom.ker f.rangeRestrict = RingHom.ker f :=
  RingHom.ker_rangeSRestrict f.toRingHom

theorem rangeSRestrict_surjective (f : S →ₐ[R] T'):
    Function.Surjective (f.rangeSRestrict) :=
  fun ⟨_y, hy⟩ =>
  let ⟨x, hx⟩ := hy
  ⟨x, SetCoe.ext hx⟩

theorem rangeS_top_iff_surjective {f : S →ₐ[R] T'} :
    f.range = (⊤ : Subalgebra R T') ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans <| Iff.trans (by rw [coe_range, Algebra.coe_top]) Set.range_iff_surjective

theorem rangeS_top_of_surjective (f : S →ₐ[R] T') (hf : Function.Surjective f) :
    f.rangeS = ⊤ :=
  rangeS_top_iff_surjective.2 hf

/-- The **first isomorphism theorem** for commutative rings (`AlgHom.rangeS` version). -/
noncomputable def quotientKerEquivRangeS (f : S →ₐ[R] T') :
    (S ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] f.rangeS :=
  (Ideal.quotientEquivAlgOfEq R f.ker_rangeSRestrict.symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective f.rangeSRestrict_surjective



example  {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [hFT : Algebra.FiniteType R S] :
    ∃ (A : Type u), ∃ (hCR : CommRing A), ∃ (hAlg : Algebra R A),
    ∃ (_ : A ≃ₐ[R] S), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  have : f.range ≃ₐ[R] S :=
    (range_top_of_surjective f hf) ▸ Subalgebra.topEquiv
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    f.quotientKerEquivRange.trans this, trivial⟩

example {R : Type u} [CommRing R]
  (S : Type v) [CommSemiring S] [Algebra R S] [hFT : Algebra.FiniteType R S] :
  ∃ (A : Type u), ∃ (_ : CommRing A), ∃ (_ : Algebra R A),
  ∃ (_ : A ≃ₐ[R] S), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  have : f.rangeS ≃ₐ[R] S :=
    (rangeS_top_of_surjective f hf) ▸ Subalgebra.topEquiv
--   use MvPolynomial (Fin n) R ⧸ (RingHom.ker f)
--   use Ideal.Quotient.commRing (RingHom.ker f)
  exact ⟨MvPolynomial (Fin n) R ⧸ (RingHom.ker f), Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    f.quotientKerEquivRangeS.trans this, trivial⟩

example  {R : Type u} [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (B : Subalgebra R S) [hFT : Algebra.FiniteType R B] :
    ∃ (A : Type u), ∃ (hCR : CommRing A), ∃ (hAlg : Algebra R A),
    ∃ (_ : A ≃ₐ[R] B), True := by
  obtain ⟨n, ⟨f, hf⟩⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  -- let A := MvPolynomial (Fin n) R ⧸ RingHom.ker f
  -- use A
  -- use Ideal.Quotient.commRing (RingHom.ker f)
  -- use Ideal.Quotient.algebra R
  have := f.quotientKerEquivRange
  have : f.range ≃ₐ[R] B := by
    have h := range_top
    -- (range_top_of_surjective f hf) ▸ Subalgebra.topEquiv
    sorry
  -- use f.quotientKerEquivRange.trans this
  exact ⟨_, Ideal.Quotient.commRing (RingHom.ker f), Ideal.Quotient.algebra R,
    f.quotientKerEquivRange.trans this, trivial⟩
