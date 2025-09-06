import Mathlib.LinearAlgebra.TensorProduct.Prod
import DividedPowers.PolynomialLaw.Basic2
import DividedPowers.PolynomialLaw.Basic3
import DividedPowers.PolynomialLaw.Coeff
import DividedPowers.ForMathlib.Algebra.MvPolynomial.Lemmas
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Basic
import DividedPowers.ForMathlib.LinearAlgebra.TensorProduct.Pi
import DividedPowers.PolynomialLaw.Homogeneous
import DividedPowers.PolynomialLaw.MultiCoeff
-- import DividedPowers.PolynomialLaw.Polarized

import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Polynomial.Basic

universe u

open TensorProduct Polynomial LinearMap

-- Recent additions to Mathlib
namespace LinearMap

variable {R S M N P Q : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]
  [AddCommMonoid Q] [Module R Q]
  [AddCommMonoid S] [Module R S]

@[simp]
lemma restrictScalars_self (f : M →ₗ[R] N) : f.restrictScalars R = f := rfl

@[simp]
lemma rTensor_map (f' : P →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    f'.rTensor Q (map f g x) = map (f' ∘ₗ f) g x :=
  LinearMap.congr_fun (rTensor_comp_map _ _ f g) x

@[simp]
lemma lTensor_map (g' : Q →ₗ[R] S) (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : M ⊗[R] N) :
    g'.lTensor P (map f g x) = map f (g' ∘ₗ g) x :=
  LinearMap.congr_fun (lTensor_comp_map _ _ f g) x

@[simp]
theorem map_rTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : S →ₗ[R] M) (x : S ⊗[R] N) :
    map f g (f'.rTensor _ x) = map (f.comp f') g x :=
  LinearMap.congr_fun (map_comp_rTensor _ _ _ _) x

@[simp]
lemma map_lTensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : S →ₗ[R] N) (x : M ⊗[R] S) :
    map f g (g'.lTensor M x) = map f (g ∘ₗ g') x :=
  LinearMap.congr_fun (map_comp_lTensor _ _ _ _) x

end LinearMap

namespace TensorProduct

variable (R S T M₁ M₁' M₂ M₃ : Type*)
    [CommSemiring R] [Semiring S] [Semiring T]
    [AddCommMonoid M₁] [AddCommMonoid M₁'] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Algebra R S] [Algebra R T]
    [Module R M₁] [Module R M₁']
    [Module S M₁] [Module T M₁']
    [IsScalarTower R S M₁]
    [IsScalarTower R T M₁']
    [Module R M₂] [Module R M₃]
--   M₁ ⊗[R] (M₂ × M₃) ≃ₗ[S] M₁ ⊗[R] M₂ × M₁ ⊗[R] M₃

theorem prodRight_rTensor₁ (φ : M₁ →ₗ[R] M₁') (t : M₁ ⊗[R] (M₂ × M₃)) :
    ((prodRight R T M₁' M₂ M₃)
      ((LinearMap.rTensor (M₂ × M₃) φ) t)).1 =
    (LinearMap.rTensor M₂ φ)
      ((prodRight R S M₁ M₂ M₃) t).1 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul t m => simp
  | add x y hx hy => simp [map_add, ← hx, ← hy]

theorem prodRight_rTensor₂ (φ : M₁ →ₗ[R] M₁') (t : M₁ ⊗[R] (M₂ × M₃)) :
    ((prodRight R T M₁' M₂ M₃)
      ((LinearMap.rTensor (M₂ × M₃) φ) t)).2 =
    (LinearMap.rTensor M₃ φ)
      ((prodRight R S M₁ M₂ M₃) t).2 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul t m => simp
  | add x y hx hy => simp [map_add, ← hx, ← hy]

theorem prodRight_symm_rTensor (φ : M₁ →ₗ[R] M₁') (m₂ : M₁ ⊗[R] M₂) (m₃ : M₁ ⊗[R] M₃) :
    ((prodRight R T M₁' M₂ M₃).symm
      ((LinearMap.rTensor M₂ φ) m₂, (LinearMap.rTensor M₃ φ) m₃)) =
        LinearMap.rTensor (M₂ × M₃) φ
          ((prodRight R S M₁ M₂ M₃).symm (m₂, m₃)) := by
  rw [LinearEquiv.symm_apply_eq]
  ext
  · simp [prodRight_rTensor₁ R S T]
  · simp [prodRight_rTensor₂ R S T]

end TensorProduct

namespace Polynomial

variable {R S T : Type*} [CommSemiring R] [Semiring S] [Semiring T]
  [Algebra R T] [Algebra R S] (φ : T →ₐ[R] S)

theorem monomial_comp_algHom (k : ℕ) :
    (monomial k).restrictScalars R ∘ₗ φ.toLinearMap
      = (Polynomial.mapAlgHom φ).toLinearMap ∘ₗ ((monomial k).restrictScalars R):= by
  ext; simp

theorem lcoeff_comp_mapAlgHom (k : ℕ) :
    ((lcoeff S k).restrictScalars R) ∘ₗ (mapAlgHom φ).toLinearMap
      = φ.toLinearMap ∘ₗ ((lcoeff T k).restrictScalars R) := by
  ext; simp

end Polynomial

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {N : Type*} [AddCommMonoid N] [Module R N]

/-- maps ⟨m1, m2⟩ to m1 + T m2 -/
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
    generize₂ m =
      map' (monomial 0) LinearMap.id (fst S _ _ (prodRight R S S M M m))
      + map' (monomial 1) LinearMap.id (snd S _ _ (prodRight R S S M M m)) := by
  simp [generize₂, baseChange_fst_eq_prodRight₁, baseChange_snd_eq_prodRight₂]

lemma generize₂_apply {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    generize₂ m =
      map' (monomial 0) LinearMap.id (prodRight R S S M M m).1 + map' (monomial 1) LinearMap.id (prodRight R S S M M m).2 := by
  simp [generize₂, baseChange_fst_eq_prodRight₁, baseChange_snd_eq_prodRight₂]

theorem generize₂_rTensor_eq_rTensor_mapAlgHom_generize₂
    {S : Type*} [CommSemiring S] [Algebra R S]
    {S' : Type*} [CommSemiring S'] [Algebra R S']
    (φ : S →ₐ[R] S') (m : S ⊗[R] (M × M)) :
    generize₂ ((LinearMap.rTensor (M × M) φ.toLinearMap) m)
       = LinearMap.rTensor M (mapAlgHom φ) (generize₂ m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp [generize₂, map'_coe, map_tmul]
  | add x y hx hy => simp [map_add, ← hx, ← hy]

noncomputable def dividedDifferential (k : ℕ) : (M →ₚₗ[R] N) →ₗ[R] (M × M →ₚₗ[R] N) where
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

lemma dividedDifferential_ground_eq_coeff (k : ℕ) (f : M →ₚₗ[R] N) (m m' : M) :
    f.dividedDifferential k (m, m') =
      Polynomial.scalarRTensor R N (f.toFun' (Polynomial R)
          ((1 : Polynomial R) ⊗ₜ[R] m + Polynomial.X (R := R) ⊗ₜ[R] m')) k := by
  simp [dividedDifferential, generize₂, add_apply, coe_comp, coe_mk, AddHom.coe_mk,
    Function.comp_apply, ground_apply, baseChange_tmul, fst_apply, map_tmul,
    monomial_zero_left, map_one, id_coe, id_eq, snd_apply, monomial_one_one_eq_X,
    scalarRTensor_apply]

lemma dividedDifferential_eq_coeff' (k : ℕ) (f : M →ₚₗ[R] N)
    (S : Type u) [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M) :
    (f.dividedDifferential k).toFun' S
      ((prodRight R S S M M).symm (m, m')) =
      ((lcoeff S k).restrictScalars R).rTensor N
        (f.toFun' (Polynomial S)
          (((monomial 0).restrictScalars R).rTensor M m +
            ((monomial 1).restrictScalars R).rTensor M m'))
          := by
  simp [dividedDifferential, map'_coe, generize₂]
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

lemma dividedDifferential_eq_coeff (k : ℕ) (f : M →ₚₗ[R] N)
    (S : Type*) [CommSemiring S] [Algebra R S] (m m' : S ⊗[R] M) :
    (f.dividedDifferential k).toFun S
      ((prodRight R S S M M).symm (m, m')) =
      ((lcoeff S k).restrictScalars R).rTensor N
        (f.toFun (Polynomial S)
          (((monomial 0).restrictScalars R).rTensor M m +
            ((monomial 1).restrictScalars R).rTensor M m'))
          := by
  suffices ∃ (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (m₁ m₁' : (MvPolynomial (Fin n) R) ⊗[R] M),
    m = φ.toLinearMap.rTensor M m₁ ∧ m' = φ.toLinearMap.rTensor M m₁' by
    obtain ⟨n, φ, m₁, m₁', h₁, h₁'⟩ := this
    simp [h₁, h₁']
    simp only [← LinearMap.rTensor_comp_apply]
    simp only [monomial_comp_algHom]
    simp only [LinearMap.rTensor_comp_apply]
    rw [← map_add, ← f.isCompat_apply, ← LinearMap.rTensor_comp_apply]
    rw [prodRight_symm_rTensor R (MvPolynomial (Fin n) R) S]
    rw [← PolynomialLaw.isCompat_apply]
    simp only [toFun_eq_toFun', dividedDifferential_eq_coeff', ← rTensor_comp_apply]
    simp [lcoeff_comp_mapAlgHom]
  set mm' := (prodRight R S S M M).symm (m, m') with hmm'
  have hm : m = (prodRight R S S M M mm').1 := by simp [hmm']
  have hm' : m' = (prodRight R S S M M mm').2 := by simp [hmm']
  obtain ⟨n, φ, t, ht⟩ := exists_lift mm'
  have := (prodRight R (MvPolynomial (Fin n) R) _ M M t).1
  use n, φ, (prodRight R (MvPolynomial (Fin n) R) _ _ _ t).1, (prodRight R (MvPolynomial (Fin n) R) _ _ _ t).2
  simp [hm, hm', ← ht,
    prodRight_rTensor₁ R (MvPolynomial (Fin n) R) S,
    prodRight_rTensor₂ R (MvPolynomial (Fin n) R) S]

/-- The nth divided partial derivative of `f` at `x`. -/
noncomputable def dividedPartialDerivative (k : ℕ) (x : M) :
    (M →ₚₗ[R] N) →ₗ[R] (M →ₚₗ[R] N) where
  toFun f := (f.dividedDifferential k).comp ((inl R M M).toPolynomialLaw + (inr R M M).toPolynomialLaw.comp (const R M M x))
  map_add' f g := by
    ext S _ _ sm
    simp [map_add, comp_toFun', add_def, Function.comp_apply, Pi.add_apply]
  map_smul' r f := by
    ext S _ _ sm
    simp [map_smul, comp_toFun', smul_def, add_def, Function.comp_apply, Pi.add_apply,
      Pi.smul_apply, RingHom.id_apply]

-- Add the same for `dividedDifferential`?

theorem dividedPartialDerivative_zero (x : M) (f : M →ₚₗ[R] N) :
    f.dividedPartialDerivative 0 x = f := by
  ext S _ _ m
  unfold dividedPartialDerivative
  simp [comp_toFun', const, toPolynomialLaw, LinearMap.baseChange, inl, inr, LinearMap.prod]
  simp [dividedDifferential_ground_eq_coeff]
  simp [comp_toFun', const, toPolynomialLaw, inl, inr,
    LinearMap.baseChange, LinearMap.prod]


  simp only [generize₂_apply, fst_apply, map'_coe, snd_apply, coe_mk, AddHom.coe_mk,
    toPolynomialLaw, LinearMap.baseChange, inl, const, comp_toFun', add_def, Function.comp_apply,
    Pi.add_apply, AlgebraTensorModule.map_tmul, id_coe, id_eq, coe_inr, map_add, prodRight_tmul,
    tmul_zero, Prod.fst_add, add_zero, Prod.snd_add, map_tmul, coe_restrictScalars]
  have : ⇑(TensorProduct.map ((lcoeff S 0) : S[X] →ₗ[R] S) (LinearMap.id (R := R) (M := N)))
    = ⇑(((aeval (R := S) (0 : S)).restrictScalars R).toLinearMap.rTensor N) := by
    ext m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul f m => simp [coeff_zero_eq_eval_zero]
    | add x y hx hy => simp [map_add, ← hx, ← hy]
  rw [this, isCompat_apply']
  congr 1
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy =>
    /-simp [Prod.add_def, map_add] at hx hy ⊢

    erw [map_add, map_add, map_add, map_add]
    erw [map_add]
    rw [add_add_add_comm, ← hx, ← hy]
    congr
    apply congr_arg -/
    sorry

theorem dividedPartialDerivative_smul_right (k : ℕ) (x : M) (r : R) (f : M →ₚₗ[R] N) :
    f.dividedPartialDerivative k (r • x) = r ^ k • f.dividedPartialDerivative k x := by
  sorry

theorem dividedPartialDerivative_one_of_LinearMap (x : M) (f : M →ₗ[R] N) :
    f.toPolynomialLaw.dividedPartialDerivative 1 x = f.toPolynomialLaw := sorry

theorem dividedPartialDerivative_commute (k : ℕ) (x : M) (l : ℕ) (y : M) :
    Commute (dividedPartialDerivative (N := N) (R := R) k x) (dividedPartialDerivative l y) :=
  sorry

theorem locFinite_dividedPartialDerivative (x : M) (f : M →ₚₗ[R] N) :
    LocFinsupp (fun k ↦ f.dividedPartialDerivative k x) :=
  sorry

def translation (a : M) : (M →ₚₗ[R] N) →ₗ[R] (M →ₚₗ[R] N) where
  toFun f := {
    toFun' S _ _ m := f.toFun' S (m + 1 ⊗ₜ[R] a)
    isCompat' := sorry }
  map_add' := sorry
  map_smul' := sorry

-- Taylor formula
example (f : M →ₚₗ[R] N) :
    lfsum (fun k ↦ f.dividedDifferential k)  =
      f.comp (fst R M M + snd R M M).toPolynomialLaw :=
  sorry

-- Taylor formula
theorem lfsum_dividedPartialDerivative (x : M) (f : M →ₚₗ[R] N) :
    lfsum (fun k ↦ f.dividedPartialDerivative k x)  = f.translation x :=
  sorry

-- Roby63, pg 240 (Prop. II.2)
lemma dividedPartialDerivative_comp {n p : ℕ} (x : M) (f : M →ₚₗ[R] N) :
    dividedPartialDerivative n x (dividedPartialDerivative p x f) =
      (n.choose p) * dividedPartialDerivative (n + p) x f := by
  sorry

end  PolynomialLaw

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
