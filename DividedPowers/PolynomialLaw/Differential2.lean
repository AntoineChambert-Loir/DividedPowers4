import DividedPowers.ForMathlib.Algebra.Module.LinearMap.Defs
import DividedPowers.ForMathlib.RingTheory.TensorProduct.Polynomial
import DividedPowers.PolynomialLaw.Linear
import DividedPowers.PolynomialLaw.LocFinsupp
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Prod

/-! # Differentials of polynomial laws (work in progress)

In this file we propose a second approach for the definition of the differential of a polynomial
law, using the characterization right after [Roby63, definition in pg. 239].

## Main definitions

* `PolynomialLaw.dividedDifferential'`: the differential of order `k` of a polynomial law,
  denoted by `D^k f` in [Roby63].

* `PolynomialLaw.dividedPartialDerivative'`: the `n`th divided partial derivative of `f` at `x`.

## TODO

* Prove the Taylor formula for polynomial laws [Roby63, Prop. II.2]

-/

universe u

open TensorProduct Polynomial LinearMap

namespace TensorProduct

variable (R : Type u) (M₁ : Type*) [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]

theorem prodRight_symm_apply {S : Type u} [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M₁) :
    (prodRight R S S M₁ M₁).symm (m, m') =
      (inl R M₁ M₁).toPolynomialLaw.toFun' S m + (inr R M₁ M₁).toPolynomialLaw.toFun' S m' := rfl

end TensorProduct

namespace Polynomial

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T]
  [Algebra R T] [Algebra R S] (φ : T →ₐ[R] S)

theorem monomial_comp_algHom (k : ℕ) :
    (monomial k).restrictScalars R ∘ₗ φ.toLinearMap =
      (Polynomial.mapAlgHom φ).toLinearMap ∘ₗ ((monomial k).restrictScalars R):= by
  ext; simp

theorem lcoeff_comp_mapAlgHom (k : ℕ) :
    ((lcoeff S k).restrictScalars R) ∘ₗ (mapAlgHom φ).toLinearMap =
      φ.toLinearMap ∘ₗ ((lcoeff T k).restrictScalars R) := by
  ext; simp

end Polynomial

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- maps `(m1, m2)` to `m1 + T m2` -/
noncomputable def generize₂ {S : Type*} [CommSemiring S] [Algebra R S] :
    S ⊗[R] (M × M) →ₗ[S] Polynomial S ⊗[R] M :=
  map' (monomial 0) LinearMap.id ∘ₗ baseChange S (fst R M M) +
    map' (monomial 1) LinearMap.id ∘ₗ baseChange S (snd R M M)

lemma baseChange_fst_eq_prodRight₁
    {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    (baseChange S (fst R M M)) m = fst S _ _ ((prodRight R S S M M) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp [map_add, hx, hy]

lemma baseChange_snd_eq_prodRight₂
    {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    (baseChange S (snd R M M)) m = snd S _ _ ((prodRight R S S M M) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp [map_add, hx, hy]

lemma generize₂_apply' {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    generize₂ m = map' (monomial 0) LinearMap.id (fst S _ _ (prodRight R S S M M m)) +
      map' (monomial 1) LinearMap.id (snd S _ _ (prodRight R S S M M m)) := by
  simp [generize₂, baseChange_fst_eq_prodRight₁, baseChange_snd_eq_prodRight₂]

lemma generize₂_apply {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    generize₂ m =
      map' (monomial 0) LinearMap.id (prodRight R S S M M m).1 +
        map' (monomial 1) LinearMap.id (prodRight R S S M M m).2 := by
  simp [generize₂_apply']

theorem generize₂_rTensor_eq_rTensor_mapAlgHom_generize₂
    {S : Type*} [CommSemiring S] [Algebra R S] {S' : Type*} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (m : S ⊗[R] (M × M)) :
    generize₂ ((LinearMap.rTensor (M × M) φ.toLinearMap) m) =
      LinearMap.rTensor M (mapAlgHom φ) (generize₂ m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp [generize₂, map'_coe, map_tmul]
  | add x y hx hy => simp [map_add, ← hx, ← hy]

/-- The differential of order `k` of a polynomial law, denoted by `D^k f` in [Roby63]. -/
noncomputable def dividedDifferential' (k : ℕ) : (M →ₚₗ[R] N) →ₗ[R] (M × M →ₚₗ[R] N) where
  toFun f := {
    toFun' S _ _ m := ((lcoeff S k).restrictScalars R).rTensor N (f.toFun' _ (generize₂ m))
    isCompat' {S} _ _ {S'} _ _ φ := by
      ext m
      simp only [Function.comp_apply, generize₂_rTensor_eq_rTensor_mapAlgHom_generize₂]
      erw [← f.isCompat_apply']
      generalize f.toFun' S[X] (generize₂ m) = n
      induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul s n => simp }
  map_add' f g := by ext; simp
  map_smul' s f := by ext; simp

lemma dividedDifferential'_ground_eq_coeff (k : ℕ) (f : M →ₚₗ[R] N) (m m' : M) :
    f.dividedDifferential' k (m, m') =
      Polynomial.scalarRTensor R N (f.toFun' (Polynomial R)
        ((1 : Polynomial R) ⊗ₜ[R] m + Polynomial.X (R := R) ⊗ₜ[R] m')) k := by
  simp [dividedDifferential', generize₂, add_apply, coe_comp, coe_mk, AddHom.coe_mk,
    Function.comp_apply, ground_apply, baseChange_tmul, fst_apply, map_tmul,
    monomial_zero_left, map_one, id_coe, id_eq, snd_apply, monomial_one_one_eq_X,
    scalarRTensor_apply]

lemma dividedDifferential'_eq_coeff' (k : ℕ) (f : M →ₚₗ[R] N)
    (S : Type u) [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M) :
    (f.dividedDifferential' k).toFun' S ((prodRight R S S M M).symm (m, m')) =
      ((lcoeff S k).restrictScalars R).rTensor N
        (f.toFun' (Polynomial S) (((monomial 0).restrictScalars R).rTensor M m +
          ((monomial 1).restrictScalars R).rTensor M m')) := by
  simp [dividedDifferential', map'_coe, generize₂]
  congr 2
  set mm' := (prodRight R S S M M).symm (m, m') with hmm'
  have hm : m = (prodRight R S S M M mm').1 := by simp [hmm']
  have hm' : m' = (prodRight R S S M M mm').2 := by simp [hmm']
  simp only [hm, hm']
  induction mm' using TensorProduct.induction_on with
  | zero => simp
  | tmul s mm' => simp
  | add x y hx hy =>
    simp [map_add, add_add_add_comm, ← hx, ← hy]

lemma dividedDifferential'_eq_coeff (k : ℕ) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M) :
    (f.dividedDifferential' k).toFun S ((prodRight R S S M M).symm (m, m')) =
      ((lcoeff S k).restrictScalars R).rTensor N
        (f.toFun (Polynomial S) (((monomial 0).restrictScalars R).rTensor M m +
          ((monomial 1).restrictScalars R).rTensor M m')) := by
  suffices ∃ (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
      (m₁ m₁' : (MvPolynomial (Fin n) R) ⊗[R] M),
      m = φ.toLinearMap.rTensor M m₁ ∧ m' = φ.toLinearMap.rTensor M m₁' by
    obtain ⟨n, φ, m₁, m₁', h₁, h₁'⟩ := this
    simp [h₁, h₁']
    simp only [← LinearMap.rTensor_comp_apply, monomial_comp_algHom]
    simp only [LinearMap.rTensor_comp_apply]
    rw [← map_add, ← f.isCompat_apply, ← LinearMap.rTensor_comp_apply,
      prodRight_symm_rTensor R (MvPolynomial (Fin n) R) S, ← PolynomialLaw.isCompat_apply]
    simp [toFun_eq_toFun', dividedDifferential'_eq_coeff', ← rTensor_comp_apply,
      lcoeff_comp_mapAlgHom]
  set mm' := (prodRight R S S M M).symm (m, m') with hmm'
  have hm : m = (prodRight R S S M M mm').1 := by simp [hmm']
  have hm' : m' = (prodRight R S S M M mm').2 := by simp [hmm']
  obtain ⟨n, φ, t, ht⟩ := exists_lift mm'
  use n, φ, (prodRight R (MvPolynomial (Fin n) R) _ _ _ t).1,
    (prodRight R (MvPolynomial (Fin n) R) _ _ _ t).2
  simp [hm, hm', ← ht, prodRight_rTensor₁ R (MvPolynomial (Fin n) R) S,
    prodRight_rTensor₂ R (MvPolynomial (Fin n) R) S]

variable (S : Type*) [CommSemiring S] [Algebra R S] (f : M →ₚₗ[R] N)

-- Roby63, pg 239
lemma dividedDifferential'_smul_right' (k : ℕ) (f : M →ₚₗ[R] N) (r : R)
    (S : Type u) [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M) :
    (f.dividedDifferential' k).toFun' S ((prodRight R S S M M).symm (m, r • m')) =
      r ^ k • (f.dividedDifferential' k).toFun' S ((prodRight R S S M M).symm (m, m')) := by
  rw [dividedDifferential'_eq_coeff', dividedDifferential'_eq_coeff']
  simp only [← map_smul]
  sorry

-- Roby63, pg 239
lemma dividedDifferential'_smul_right (k : ℕ) (f : M →ₚₗ[R] N) (r : R)
    (S : Type*) [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M) :
    (f.dividedDifferential' k).toFun S ((prodRight R S S M M).symm (m, r • m')) =
      r ^ k • (f.dividedDifferential' k).toFun S ((prodRight R S S M M).symm (m, m')) := by
  sorry

/-- The nth divided partial derivative of `f` at `x`. -/
noncomputable def dividedPartialDerivative' (k : ℕ) (x : M) :
    (M →ₚₗ[R] N) →ₗ[R] (M →ₚₗ[R] N) where
  toFun f := (f.dividedDifferential' k).comp ((inl R M M).toPolynomialLaw +
    (inr R M M).toPolynomialLaw.comp (const R M M x))
  map_add' f g := by
    ext S _ _ sm
    simp [map_add, comp_toFun', add_def, Function.comp_apply, Pi.add_apply]
  map_smul' r f := by
    ext S _ _ sm
    simp [map_smul, comp_toFun', smul_def, add_def, Function.comp_apply, Pi.add_apply,
      Pi.smul_apply, RingHom.id_apply]

lemma dividedPartialDerivative'_apply' (k : ℕ) (x : M) (f : M →ₚₗ[R] N)
    {S : Type u} [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    ((dividedPartialDerivative' k x) f).toFun' S m =
      ((dividedDifferential' k) f).toFun' S ((inl R M M).toPolynomialLaw.toFun' S m +
        (inr R M M).toPolynomialLaw.toFun' S (1 ⊗ₜ[R] x)) := by
  unfold dividedPartialDerivative'
  simp [comp_toFun', const]

lemma dividedPartialDerivative'_apply (k : ℕ) (x : M) (f : M →ₚₗ[R] N)
    {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) :
    ((dividedPartialDerivative' k x) f).toFun S m =
      ((dividedDifferential' k) f).toFun S ((inl R M M).toPolynomialLaw.toFun S m +
        (inr R M M).toPolynomialLaw.toFun S (1 ⊗ₜ[R] x)):= by
  sorry

theorem dividedPartialDerivative'_zero (x : M) (f : M →ₚₗ[R] N) :
    f.dividedPartialDerivative' 0 x = f := by
  ext S _ _ m
  rw [dividedPartialDerivative'_apply']
  simp only [toPolynomialLaw, LinearMap.baseChange, inl]
  convert dividedDifferential'_eq_coeff' 0 f S m (1 ⊗ₜ[R] x)
  simp only [rTensor_tmul, coe_restrictScalars]
  let c0 : S[X] →ₐ[R] S := {
    lcoeff S 0 with
    map_zero' := by simp
    map_one' := by simp
    map_mul' := by simp
    commutes' := by simp }
  have hc0 : c0.toLinearMap = lcoeff S 0 := rfl
  rw [← hc0, isCompat_apply']
  congr
  simp only [hc0, map_add, ← rTensor_comp_apply, rTensor_tmul, coe_restrictScalars, lcoeff_apply,
    coeff_monomial_succ, zero_tmul, add_zero]
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp
  | tmul => simp

theorem dividedPartialDerivative'_smul_right (k : ℕ) (x : M) (r : R) (f : M →ₚₗ[R] N) :
    f.dividedPartialDerivative' k (r • x) = r ^ k • f.dividedPartialDerivative' k x := by
  ext S _ _ m
  simp only [smul_def, Pi.smul_apply, dividedPartialDerivative'_apply', tmul_smul]
  rw [← prodRight_symm_apply, ← prodRight_symm_apply, dividedDifferential'_smul_right']

theorem dividedPartialDerivative'_one_of_LinearMap (x : M) (f : M →ₗ[R] N) :
    f.toPolynomialLaw.dividedPartialDerivative' 1 x = f.toPolynomialLaw := by
  ext S _ _ m
  unfold dividedPartialDerivative'
  sorry

theorem dividedPartialDerivative'_commute (k : ℕ) (x : M) (l : ℕ) (y : M) :
    Commute (dividedPartialDerivative' (N := N) (R := R) k x) (dividedPartialDerivative' l y) :=
  sorry

theorem locFinite_dividedPartialDerivative' (x : M) (f : M →ₚₗ[R] N) :
    LocFinsupp (fun k ↦ f.dividedPartialDerivative' k x) :=
  sorry

-- Taylor formula
example (f : M →ₚₗ[R] N) :
    lfsum (fun k ↦ f.dividedDifferential' k) = f.comp (fst R M M + snd R M M).toPolynomialLaw :=
  sorry

-- Taylor formula
theorem lfsum_dividedPartialDerivative' (x : M) (f : M →ₚₗ[R] N) :
    lfsum (fun k ↦ f.dividedPartialDerivative' k x) = f.translation x :=
  sorry

-- Roby63, pg 240 (Prop. II.2)
lemma dividedPartialDerivative'_comp {n p : ℕ} (x : M) (f : M →ₚₗ[R] N) :
    dividedPartialDerivative' n x (dividedPartialDerivative' p x f) =
      (n.choose p) * dividedPartialDerivative' (n + p) x f := by
  sorry

end  PolynomialLaw


-- OLD

section Junk

variable {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (f : M →ₚₗ[R] N)
  (σ : Type*)  [DecidableEq σ]

variable {S : Type*} [CommSemiring S] [Algebra R S]

example : S ⊗[R] MvPolynomial σ R ≃ₐ[S] MvPolynomial σ S :=
  have := MvPolynomial.scalarRTensorAlgEquiv (R := R) (σ := σ) (N := S)
  sorry

example : S ⊗[R] M →ₗ[S] S ⊗[R] (M × M) :=
  (inl R M M).baseChange S -- or inr

example : S ⊗[R] (M × M) ≃ₗ[S] (S ⊗[R] M) × (S ⊗[R] M) :=
  prodRight R S S M M

noncomputable example (u : S →ₗ[R] Polynomial S) :
    S ⊗[R] M →ₗ[R] (Polynomial S) ⊗[R] M :=
  rTensor M u

noncomputable example (u : S →ₗ[S] Polynomial S) :
    S ⊗[R] M →ₗ[S] (Polynomial S) ⊗[R] M :=
  map' u LinearMap.id

noncomputable example : S →ₗ[S] Polynomial S :=
  Polynomial.monomial 1

example : M × M →ₗ[R] M := by
  exact snd R M M

example : S ⊗[R] (M × M) →ₗ[S] S ⊗[R] M :=
  baseChange S (snd R M M)

example : Polynomial S →ₗ[S] S :=
  lcoeff S 1

noncomputable example : Polynomial S ⊗[R] N →ₗ[S] S ⊗[R] N :=
  map' (lcoeff S 1) LinearMap.id

noncomputable example
    {S : Type*} [CommSemiring S] [Algebra R S]
    {S' : Type*} [CommSemiring S'] [Algebra R S'] (φ : S →ₐ[R] S') :
      Polynomial S →ₐ[R] Polynomial S' :=
  mapAlgHom φ

example : S ⊗[R] (M × M) ≃ₗ[S] (S ⊗[R] M) × (S ⊗[R] M) := by
  exact prodRight R S S M M

end Junk
