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
    (baseChange S (fst R M M)) m = ((prodRight R S S M M) m).1 := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp [map_add, hx, hy]

lemma baseChange_snd_eq_prodRight₂
    {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    (baseChange S (snd R M M)) m = ((prodRight R S S M M) m).2 := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp
  | add x y hx hy => simp [map_add, hx, hy]

lemma generize₂_apply {S : Type*} [CommSemiring S] [Algebra R S] (m : S ⊗[R] (M × M)) :
    generize₂ m =
      map' (monomial 0) LinearMap.id (prodRight R S S M M m).1
      + map' (monomial 1) LinearMap.id (prodRight R S S M M m).2 := by
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
    toFun' S _ _ m := map' (lcoeff S k) LinearMap.id (f.toFun' _ (generize₂ m))
    isCompat' {S} _ _ {S'} _ _ φ := by
      ext m
      simp [generize₂_rTensor_eq_rTensor_mapAlgHom_generize₂]
      simp only [map'_coe]
      erw [← f.isCompat_apply']
      generalize f.toFun' S[X] (generize₂ m) = n
      simp [rTensor_map, map_rTensor]
      induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp [map_add, hx, hy]
      | tmul s n => simp }
  map_add' f g := by ext; simp
  map_smul' s f := by ext; simp

lemma dividedDifferential_eq_coeff (k : ℕ) (f : M →ₚₗ[R] N) (m m' : M) :
    f.dividedDifferential k (m, m') =
      Polynomial.scalarRTensor R N (f.toFun' (Polynomial R)
          ((1 : Polynomial R) ⊗ₜ[R] m + Polynomial.X (R := R) ⊗ₜ[R] m')) k := by
  simp only [dividedDifferential, map', generize₂, add_apply, coe_comp, coe_mk, AddHom.coe_mk, Function.comp_apply,
    ground_apply, baseChange_tmul, fst_apply, map_tmul, coe_restrictScalars, monomial_zero_left,
    map_one, id_coe, id_eq, snd_apply]
  simp only [scalarRTensor_apply, EmbeddingLike.apply_eq_iff_eq]
  rfl

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
    f.dividedPartialDerivative 0 x = f := sorry

theorem dividedPartialDerivative_smul_right (k : ℕ) (x : M) (r : R) (f : M →ₚₗ[R] N) :
    f.dividedPartialDerivative k (r • x) = r ^ k • f.dividedPartialDerivative k x := sorry

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

end Junk
