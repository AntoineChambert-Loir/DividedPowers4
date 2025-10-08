/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import DividedPowers.PolynomialLaw.BiHomogeneous
import DividedPowers.PolynomialLaw.MultiHomogeneous

/-! # The polarized of a polynomial law.

Given a polynomial law `f : M →ₚₗ[R] N` and an integer `n`, Roby defines the *polarized* of order
`n` of `f` as the polynomial law `Π_n f : M ^ n →ₚₗ[R] N` obtained by composing `f` and
`(m_1, ..., m_n) ↦ ∑_i m_i`.

We provide two versions of this definitions: `polarizedProd` for `n=2`, as a polynomial law
`(M × M) →ₚₗ[R] N`, and `polarized` for general `n`, as a polynomial law `(Π (_ : ι), M) →ₚₗ[R] N`,
where `ι` is a fintype.

## Main definitions

* `PolynomialLaw.polarizedProd`: given a polynomial law `f : M →ₚₗ[R] N`, `f.polarizedProd`
is the polynomial law `(M × M) →ₚₗ[R] N` obtained by composing `f` and `fst R M M + snd R M M`.
This is denoted by `Π_2` in [Roby63 II.1].

* `PolynomialLaw.polarizedProd_biComponent`: the bihomogeneous component of bidegree `n : ℕ × ℕ` of
  `f.polarized n`. This is denoted by `Π^{n.1, n.2} f` in Roby63.

* `PolynomialLaw.polarizedProd`: given a polynomial law `f : M →ₚₗ[R] N` and a finite type `ι`,
the `ι`-polarized of `f` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] N` obtained by composing `f`
and `sum_proj R M ι`. This is denoted by `Π_p` in Roby63 (where `p` corresponds to the size of `ι`).


* `PolynomialLaw.polarized_multiComponent`: the multihomogeneous component of multidegree
  `n : ι →₀ ℕ` of `f.polarized ι`. This is denoted by `Π^{n_1, ..., n_p} f` in Roby63.

## Main results

* `PolynomialLaw.isHomogeneous_polarizedProd`: if `f` is homogeneous, then `f.polarizedProd` is
  homogeneous of the same degree.

* `PolynomialLaw.locFinsupp_polarizedProd_biComponent`: the family
  `fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f` has locally finite support.

* `PolynomialLaw.isHomogeneous_polarized`: if `f` is homogeneous, then `f.polarized` is
  homogeneous of the same degree.

* `PolynomialLaw.locFinsupp_polarized_multiComponent`: the family
  `fun (p : ℕ) ↦ polarized_multiComponent (map_pair n p) f` has locally finite support.

-/

noncomputable section

open MvPolynomial TensorProduct

universe u

variable {ι : Type*} {R : Type u} [CommSemiring R] {M M' N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid M'] [Module R M'] [AddCommMonoid N] [Module R N] (f : M →ₚₗ[R] N) (n p : ℕ)

namespace PolynomialLaw

section PolarizedProd

open LinearMap

/-- Given a polynomial law `f : M →ₚₗ[R] N`, `f.polarizedProd`
is the polynomial law `(M × M) →ₚₗ[R] N` obtained by composing `f` and `fst R M M + snd R M M`.
This is denoted by `Π_2` in [Roby63 II.1]. -/
def polarizedProd : (M →ₚₗ[R] N) →ₗ[R] (M × M →ₚₗ[R] N) where
  toFun f := f.comp (fst R M M + snd R M M).toPolynomialLaw
  map_add' f g := by
    ext S _ _ sm
    simp [comp_toFun']
  map_smul' r f := by
    ext S _ _ sm
    simp [comp_toFun']

lemma polarizedProd_apply (m : M × M) : f.polarizedProd m = f (m.fst + m.snd):= by
  simp only [polarizedProd, fst, snd, coe_mk, AddHom.coe_mk, ground_apply, comp_toFun',
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma map_add_eq_polarizedprod_two_apply (m m' : M) :
    f (m + m') = (f.polarizedProd) (m, m') := by
  simp only [polarizedProd_apply]

lemma polarizedProd_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (M × M)} : (polarizedProd f).toFun' S m =
      f.toFun' S (((prodRight R R S M M) m).fst + ((prodRight R R S M  M) m).snd) := by
  simp [polarizedProd, comp_toFun']
  congr 1
  simp only [toPolynomialLaw_toFun']
  rw [baseChange_fst_eq_prodRight_fst, baseChange_snd_eq_prodRight_snd]

variable {f p}

lemma isHomogeneous_polarizedProd (hf : IsHomogeneous p f) :
    IsHomogeneous p (polarizedProd f) := fun S _ _ s m ↦ by
  simp [polarizedProd_toFun'_apply,
    ← hf S s ((((prodRight R R S M M) m).fst + ((prodRight R R S M  M) m).snd)),
      smul_add, prodRight_smul]

-- Roby63, example in pg 234
lemma coeff_polarizedProd_eq_zero_of_ne {n : ℕ} (m : (Fin n) → M × M) (d : (Fin n) →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≠ p) (hf : IsHomogeneous p f) :
    coeff m (polarizedProd f) d = 0 := by
  revert n
  rw [← isHomogeneous_of_coeff_iff]
  exact isHomogeneous_polarizedProd hf

/-- The bihomogeneous component of bidegree `n : ℕ × ℕ` of `f.polarized n`.
  This is denoted by `Π^{n.1, n.2} f` in Roby63. -/
abbrev polarizedProd_biComponent (n : ℕ × ℕ) (f : PolynomialLaw R M N) :
    PolynomialLaw R (M × M) N := PolynomialLaw.biComponent n f.polarizedProd

theorem locFinsupp_polarizedProd_biComponent (f : PolynomialLaw R M N) :
    LocFinsupp (fun (p : ℕ) ↦ polarizedProd_biComponent (p, n) f) := fun S _ _ m ↦ by
  have hss : (fun p ↦ (p, n)) ''
      (Function.support fun i ↦ (biComponent (i, n) (polarizedProd f)).toFun' S m) ⊆
        (Function.support fun d ↦ (biComponent d (polarizedProd f)).toFun' S m) := fun _ hd ↦ by
    obtain ⟨x, hx, rfl⟩ := hd
    simpa [biComponent_apply_toFun', finTwoArrowEquiv', Fin.isValue,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  exact ((LocFinsupp_biComponent f.polarizedProd _ _ ).subset hss).of_finite_image
    (fun _ _ _ _ h ↦ by simpa using h)

end PolarizedProd

section Polarized

open LinearMap

lemma proj_apply (i : ι) (m : ι → M) :
    (proj (R:= R) i).toPolynomialLaw m = m i := by
  simp [toPolynomialLaw_ground_apply]

lemma proj_toFun'_apply {S : Type u} [CommSemiring S] [Algebra R S] (i : ι) {m : S ⊗[R] (ι → M)} :
    (proj i).toPolynomialLaw.toFun' S m = (piRightHom R R S fun _ ↦ M) m i := by
  simp only [proj]
  induction m using TensorProduct.induction_on with
  | zero => simp [toPolynomialLaw_toFun']
  | tmul => simp [toPolynomialLaw_toFun']
  | add m m' hm hm' =>
    simp only [toPolynomialLaw_toFun', map_add, Pi.add_apply] at hm hm' ⊢;
    simp [hm, hm']

lemma proj_toFun_apply {S : Type*} [CommSemiring S] [Algebra R S] (i : ι) {m : S ⊗[R] (ι → M)} :
    (proj i).toPolynomialLaw.toFun S m = (piRightHom R R S fun _ ↦ M) m i := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, proj_toFun'_apply,
    piRightHom_rTensor_eq_rTensor_piRightHom ψ.toLinearMap]

lemma proj_toFun'_tmul {S : Type u} [CommSemiring S] [Algebra R S] (i : ι) {m : ι → M} :
    (proj i).toPolynomialLaw.toFun' S (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m i := by
  simp [proj_toFun'_apply]

lemma proj_toFun_tmul {S : Type*} [CommSemiring S] [Algebra R S] (i : ι) {m : ι → M} :
    (proj i).toPolynomialLaw.toFun S (1 ⊗ₜ[R] m) = 1 ⊗ₜ[R] m i := by
  obtain ⟨n', ψ, q, h⟩ := exists_lift ((1 : S) ⊗ₜ[R] m)
  rw [← h, ← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, proj_toFun'_apply,
    ← piRightHom_rTensor_eq_rTensor_piRightHom ψ.toLinearMap q, h, piRightHom_tmul]

variable (ι R M) in
/-- `sum_proj ι R M` is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] M` defined as the sum of all the
coordinate laws from  `(Π (_ : ι), M)`to `M`. -/
def sum_proj : (Π (_ : ι), M) →ₚₗ[R] M := lfsum (fun i ↦ (proj i).toPolynomialLaw)

lemma sum_proj_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (ι → M)} : (sum_proj ι R M).toFun' S m =
    (∑ i, (piRight R R S fun _ ↦ M) m i) := by
  rw [sum_proj, piRight_apply, lfsum_toFun'_eq_of_locFinsupp (locFinsupp_of_fintype _),
    Finsupp.sum_fintype _ _ (by intro; rfl)]
  exact Finset.sum_congr rfl (fun i _ ↦ proj_toFun'_apply i)

variable (ι) in
/-- Given a polynomial law `f : M →ₚₗ[R] N` and a finite type `ι`, the `ι`-polarized of `f`
is the polynomial law `(Π (_ : ι), M) →ₚₗ[R] N` obtained by composing `f` and `sum_proj R M ι`.
This is denoted by `Π_p` in Roby63 (where `p` corresponds to the size of `ι`). -/
def polarized : (Π (_ : ι), M) →ₚₗ[R] N := f.comp (sum_proj ι R M)

lemma polarized_apply [Fintype ι] {m : ι → M} : polarized ι f m = f (∑ (i : ι), m i):= by

  simp only [polarized, ground_apply, sum_proj, comp_toFun',
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
  congr 1
  rw [lfsum_toFun'_eq_of_locFinsupp (locFinsupp_of_fintype _),
    Finsupp.sum_fintype _ _ (by intro; rfl), tmul_sum]
  simp [Finsupp.ofSupportFinite_coe, proj_toFun'_tmul]

lemma polarized_toFun'_apply [Fintype ι] [DecidableEq ι] {S : Type u} [CommSemiring S] [Algebra R S]
    {m : TensorProduct R S (ι → M)} : (polarized ι f).toFun' S m =
      f.toFun' S (∑ i, (TensorProduct.piRight R R S fun _ ↦ M) m i) := by
  simp [polarized, comp_toFun', sum_proj_toFun'_apply]

variable {f p}

lemma isHomogeneous_polarized [Fintype ι] (hf : IsHomogeneous p f) :
    IsHomogeneous p (polarized ι f) := by
  classical
  rw [IsHomogeneous] at hf ⊢
  intro S _ _ s m
  simp only [polarized_toFun'_apply, ← hf S s (∑ (i : ι), (TensorProduct.piRight R R _ _) m i)]
  congr
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ by rw [piRight_smul_proj]; simp)

-- Roby63, example in pg 234
lemma coeff_component_eq_zero_of_ne [Fintype ι] {n : ℕ} (m : (Fin n) → ι → M) (d : (Fin n) →₀ ℕ)
    (hd : d.sum (fun _ n => n) ≠ p) (hf : IsHomogeneous p f) :
    coeff m (polarized ι f) d = 0 := by
  revert n
  rw [← isHomogeneous_of_coeff_iff]
  exact isHomogeneous_polarized hf

def map_pair (n p : ℕ) : ((Fin 2)) →₀ ℕ :=
  (Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _))

lemma map_pair_def (n p : ℕ) : map_pair n p =
  (Finsupp.ofSupportFinite (fun i ↦ match i with | 0 => p | 1 => n) (Set.toFinite _)) := rfl

/-- The multihomogeneous component of multidegree `n : ι →₀ ℕ` of `f.polarized ι`.
  This is denoted by `Π^{n_1, ..., n_p} f` in Roby63. -/
abbrev polarized_multiComponent [Fintype ι] [DecidableEq ι] (n : ι →₀ ℕ)
    (f : PolynomialLaw R M N) :
    PolynomialLaw R (Π (_ : ι), M) N := PolynomialLaw.multiComponent n (f.polarized ι)

open TensorProduct

theorem locFinsupp_polarized_multiComponent (f : PolynomialLaw R M N) :
    LocFinsupp (fun (p : ℕ) ↦ polarized_multiComponent (map_pair n p) f) := fun S _ _ m ↦ by
  set g : ℕ → ((Fin 2) →₀ ℕ) := fun p ↦ (map_pair n p)
  set s := (Function.support fun i ↦ (multiComponent (N := N) (map_pair n i)
    (polarized ((Fin 2)) f)).toFun' S m)
  have hg : Set.InjOn g s := by
    intro a ha b hb h
    simp only [map_pair, Finsupp.ext_iff, g] at h
    exact h 0
  have hss : g '' (Function.support fun i ↦ (multiComponent (map_pair n i)
      (polarized ((Fin 2)) f)).toFun' S m) ⊆
      (Function.support fun d ↦ (multiComponent (d : (Fin 2) →₀ ℕ)
        (polarized ((Fin 2)) f)).toFun' S m) := by
    intro d hd
    simp only [Set.mem_image] at hd
    obtain ⟨x, hx, rfl⟩ := hd
    simpa only [multiComponent_toFun_apply, Function.mem_support, ne_eq, g]
  apply Set.Finite.of_finite_image _ hg
  apply Set.Finite.subset _ hss
  exact LocFinsupp_multiComponent _ _ _

end Polarized

end PolynomialLaw
