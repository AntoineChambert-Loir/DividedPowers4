import DividedPowers.PolynomialMap.Basic
import DividedPowers.ForMathlib.DirectLimit
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

universe u v


variable {R : Type u} {M N : Type _} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : PolynomialMap R M N)

open TensorProduct

/-
f : M -> N application polynomiale

t dans S ⊗ M

choix d'une algèbre tf A, φ : A → S, u ∈ A ⊗ M, φ(u) = t
on pose f (t) l'image de  f(u) ∈ A ⊗ N dans S ⊗ N

seconde algèbre tf B, ψ : B → S, v ∈ B ⊗ M, ψ(v) = t

on sait que φ(u) et ψ(v) coïncident dans C ⊗ M, θ : C → S, C tf
A ⊗ B → C
u ⊗ 1 et 1 ⊗ v ont même image

f(u) = f(v) dans C ⊗ N, donc dans S ⊗ N

-/

variable (R)
theorem MvPolynomial.aeval_range (S : Type*) [CommRing S] [Algebra R S] {σ : Type*} (s : σ → S) :
  (MvPolynomial.aeval (R := R) s).range = Algebra.adjoin R (Set.range s) := by
  apply le_antisymm
  · intro x
    rintro ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using MvPolynomial.induction_on with
    | h_C a =>
      simp only [MvPolynomial.aeval_C, Algebra.mem_adjoin_iff]
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
    use MvPolynomial.X i
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

variable {R}

noncomputable def φAux {S : Type v} [CommRing S] [Algebra R S] (s : Finset S) :
    MvPolynomial (Fin s.card) R →ₐ[R] S :=
  MvPolynomial.aeval  (R := R) (fun n ↦ (s.equivFin.symm n: S))

noncomputable def φAux' {S : Type v} [CommRing S] [Algebra R S] (s : Finset S) :
    MvPolynomial (Fin s.card) R →ₐ[R] Algebra.adjoin R (s : Set S) :=
  MvPolynomial.aeval  (R := R) (fun n ↦ ⟨s.equivFin.symm n, by
    apply Algebra.subset_adjoin
    simp only [Finset.mem_coe, Finset.coe_mem]⟩)

noncomputable def liftAux (S : Type v) [CommRing S] [Algebra R S] (t : S ⊗[R] M) :
  ∃ (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M),
    t = (LinearMap.rTensor M (φAux s).toLinearMap) p := by
  choose B hB ht using TensorProduct.Algebra.exists_of_fg t
  choose s hs using hB
  choose u ht using ht
  set h : Fin s.card → B := fun n ↦ ⟨s.equivFin.symm n, by
    rw [← hs]
    apply Algebra.subset_adjoin
    simp only [Finset.mem_coe, Finset.coe_mem]⟩
  let φ := MvPolynomial.aeval (R := R) h
  have : AlgHom.range (MvPolynomial.aeval (R := R) (fun n => (Subalgebra.val B) (h n))) = B := by
    simp_rw [MvPolynomial.aeval_range, ← hs]
    congr
    apply le_antisymm
    · rintro _ ⟨i, rfl⟩; simp
    · intro x hx; simp only [Finset.mem_coe] at hx; use s.equivFin ⟨x, hx⟩; simp
  have : LinearMap.range (LinearMap.rTensor M φ.toLinearMap) = ⊤ := by
    rw [LinearMap.range_eq_top]
    apply rTensor.surjective
    rintro ⟨x, hx⟩
    rw [← MvPolynomial.comp_aeval, AlgHom.range_comp] at this
    rw [← this] at hx
    obtain ⟨b, ⟨⟨p, rfl⟩, rfl⟩⟩ := hx
    use p
    apply Subtype.coe_injective
    rfl
  have : ∃ w, (LinearMap.rTensor M φ.toLinearMap) w = u  := by
    rw [← LinearMap.mem_range, this]
    exact Submodule.mem_top
  choose p hp using this
  use s, p
  simp only [φAux]
  rw [← ht, ← hp]
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, φ, h, ← AlgHom.comp_toLinearMap, MvPolynomial.comp_aeval]
  rfl

noncomputable def PolynomialMap.toFunAux
    {S : Type v} [CommRing S] [Algebra R S] -- (t : S ⊗[R] M)
    (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M) :
   --  (_ : t = (LinearMap.rTensor M (φAux s).toLinearMap) p) :
    S ⊗[R] N :=
  LinearMap.rTensor N (φAux s).toLinearMap (f.toFun (MvPolynomial (Fin s.card) R) p)

theorem AlgHom.comp_rangeRestrict
    {R S T : Type*} [CommSemiring R]
    [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    (φ : S →ₐ[R] T) :
    (Subalgebra.val _).comp φ.rangeRestrict = φ := by
  ext; rfl

/-- Ce cas compare les deux formules lorsque les tenseurs se comparent
  dans une inclusion de sous-algèbres -/
theorem eq_of_inclusion (S : Type v) [CommRing S] [Algebra R S]
    (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M)
    (s' : Finset S) (p' : MvPolynomial (Fin s'.card) R ⊗[R] M)
    (hss' : (φAux s).range ≤ (φAux s').range)
    (hpp' : LinearMap.rTensor M ((Subalgebra.inclusion hss').comp (φAux s).rangeRestrict).toLinearMap p = LinearMap.rTensor M (φAux s').rangeRestrict.toLinearMap p') :
    f.toFunAux s p = f.toFunAux s' p' := by
  let A := MvPolynomial (Fin s.card) R ⧸ RingHom.ker (φAux s)
  let e := Ideal.quotientKerEquivRange (R := R) (φAux s)
  let A' := MvPolynomial (Fin s'.card) R ⧸ RingHom.ker (φAux s')
  let e' := Ideal.quotientKerEquivRange (R := R) (φAux s')
  let h := Subalgebra.inclusion hss'
  let φ : A →ₐ[R] A' :=
    (e'.symm.toAlgHom.comp (Subalgebra.inclusion hss')).comp e.toAlgHom
  let π : MvPolynomial (Fin s.card) R →ₐ[R] A := Ideal.Quotient.mkₐ R (RingHom.ker (φAux s))
  let π' : MvPolynomial (Fin s'.card) R →ₐ[R] A' := (Ideal.Quotient.mkₐ R (RingHom.ker (φAux s')))
  let q := LinearMap.rTensor M π.toLinearMap p
  let q' := LinearMap.rTensor M π'.toLinearMap p'
  let ψ : A →ₐ[R] S := Ideal.kerLiftAlg (φAux s)
  let ψ' : A' →ₐ[R] S := Ideal.kerLiftAlg (φAux s')
  have hφψ : ψ'.comp φ = ψ := sorry
  simp only [PolynomialMap.toFunAux]
  have hφAux : φAux s = ψ.comp π := sorry
  have hφAux' : φAux s' = ψ'.comp π' := sorry
  simp only [hφAux, hφAux', ← hφψ, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp,
    LinearMap.comp_apply]
  simp only [f.isCompat_apply]
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
  apply LinearMap.congr_arg
  apply congr_arg
  -- have hφπ : φ.comp π = φ'
  have hε' : Function.Injective (LinearMap.rTensor M e'.toAlgHom.toLinearMap) := sorry
  apply hε'
  simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
  convert hpp'
  ext p
  simp [e', φ, π]
  rfl

/-- Ce cas montrera que f.toFunAux S permet de définir f.toFun S t -/
theorem eq_of_eq (S : Type v) [CommRing S] [Algebra R S]
    (s : Finset S) (p : MvPolynomial (Fin s.card) R ⊗[R] M)
    (s' : Finset S) (p' : MvPolynomial (Fin s'.card) R ⊗[R] M)
    (h : LinearMap.rTensor M (φAux s).toLinearMap p =
          LinearMap.rTensor M (φAux s').toLinearMap p') :
    f.toFunAux s p = f.toFunAux s' p' := by

  classical
  set u := LinearMap.rTensor M (φAux s).rangeRestrict.toLinearMap p with hu
  have uFG : Subalgebra.FG (R := R) (φAux s).range := by
    rw [← Algebra.map_top]
    apply Subalgebra.FG.map
    exact (Algebra.FiniteType.mvPolynomial R (Fin s.card)).out

  set u' := LinearMap.rTensor M (φAux s').rangeRestrict.toLinearMap p' with hu'
  have u'FG : Subalgebra.FG (R := R) (φAux s').range := by
    rw [← Algebra.map_top]
    apply Subalgebra.FG.map
    exact (Algebra.FiniteType.mvPolynomial R (Fin s'.card)).out

  have huu' : LinearMap.rTensor M (Subalgebra.val _).toLinearMap u =
    LinearMap.rTensor M (Subalgebra.val _).toLinearMap u' := by
    simp only [hu, hu', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      ← AlgHom.comp_toLinearMap,
      AlgHom.comp_rangeRestrict, h]
  obtain ⟨B, hAB, hA'B, hB, h⟩ :=
    TensorProduct.Algebra.eq_of_fg_of_subtype_eq' (R := R) uFG u u'FG u' huu'
  let ⟨s'', hs''⟩ := hB
  have hs'' : B = (φAux s'').range := sorry
  have hAB' : (φAux s).range ≤ (φAux s'').range := le_trans hAB (le_of_eq hs'')
  have hA'B' : (φAux s').range ≤ (φAux s'').range := le_trans hA'B (le_of_eq hs'')
  have : ∃ q : MvPolynomial (Fin s''.card) R ⊗[R] M,
    LinearMap.rTensor M (AlgHom.toLinearMap (φAux s'').rangeRestrict) q
      = LinearMap.rTensor M ((Subalgebra.inclusion (le_of_eq hs'')).comp (Subalgebra.inclusion hAB)).toLinearMap u := sorry
  obtain ⟨q, hq⟩ := this
  rw [eq_of_inclusion f S s p s'' q hAB']
  rw [eq_of_inclusion f S s' p' s'' q hA'B']
  · rw [hq]
    simp only [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp, LinearMap.comp_apply]
    rw [← hu', h]
    simp only [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap]
    congr
  · rw [hq, hu]
    simp only [← LinearMap.comp_apply, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp]
    congr; ext; rfl


variable (R M)

private
def α (S : Type v) [CommRing S] [Algebra R S] : Type _ :=
  Σ (s : Finset S), (MvPolynomial (Fin s.card) R) ⊗[R] M

private
noncomputable def π (S : Type v) [CommRing S] [Algebra R S] :
    α R M S → S ⊗[R] M :=
  fun ⟨s, p⟩ ↦ LinearMap.rTensor M (φAux s).toLinearMap p

variable {R M}
private
noncomputable def φ (S : Type v) [CommRing S] [Algebra R S] :
  α R M S → S ⊗[R] N := fun ⟨s,p⟩ ↦ f.toFunAux s p

noncomputable def PolynomialMap.toFun' (S : Type v) [CommRing S] [Algebra R S] :
    S ⊗[R] M → S ⊗[R] N := by
  apply Function.extend (π R M S) (φ f S) (fun _ ↦ 0)

theorem φFT (S : Type v) [CommRing S] [Algebra R S] :
    Function.FactorsThrough (φ f S) (π R M S) := by
  rintro ⟨s, p⟩ ⟨s', p'⟩ h
  simp only [φ]
  apply eq_of_eq
  exact h

theorem f.toFun'_apply (S : Type v) [CommRing S] [Algebra R S] (t : S ⊗[R] M)
    (s : Finset S) (p : (MvPolynomial (Fin s.card) R) ⊗[R] M)
    (hp : t = LinearMap.rTensor M (φAux s).toLinearMap p) :
    f.toFun' S t = f.toFunAux s p := by
  simp only [PolynomialMap.toFun']
  have hp' : t = π R M S (⟨s, p⟩ : α R M S) := by rw [hp]; rfl
  rw [hp', (φFT f S).extend_apply]; rfl

/-

  p ∈ P ⊗ M       t = φ p
  I = noyau (φ : P → S), A = P/I
  π (p) ∈ A ⊗ M,   f(p) ∈ A ⊗ N   : f(t) = j( f(p) )

  p' ∈ P' ⊗ M     t' = φ' p
  I' = noyau (φ' : P' → S), A' = P'/I'
  π(p') ∈ A' ⊗ M, f(p') ∈ A ⊗ N  : f(t') = j' (f(p'))

  φ p et φ p' égaux dans B ⊗ M, k : A → B, k' : A' → B'
  prouver k f(p) = k' f(p'))

  P ⊗ M → Q ⊗ M

  A ⊗ M → B ⊗ M ← A' ⊗ M      p → k(p) = q = k' (p') ← p'

  A ⊗ N → B ⊗ N ← A' ⊗ N

  k (f(p) ) = f(q) = k'(f(p'))
-/
