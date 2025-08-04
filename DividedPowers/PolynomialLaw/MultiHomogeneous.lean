/- Copyright ACL & MIdFF 2024 -/

import DividedPowers.PolynomialLaw.Homogeneous
import DividedPowers.PolynomialLaw.MultiCoeff
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.TensorProduct.Pi

import Mathlib.LinearAlgebra.Multilinear.Basic

universe u uι

/- # Multihomogeneous components of a polynomial map

Let `S` be an `R`-algebra and let `j : S →ₐ[S] S[X]` be the canonical algebra map.

For `m : S ⊗[R] M`, we consider the element `X • (j m) : S[X] ⊗[R] M`
and its image `f.toFun' S[X] (X • (j m)) : S[X] ⊗[R] N`.
The components of `f` are defined so that
`f.toFun' S[X] (X • (j m)) = ∑ X ^ p • (j ((f.multiComponent n).toFun' S m))`.

If one consider the morphism of evaluation at 1, `ε : S[X] →ₐ[R] S`,
we have `ε ∘ j = @id S`, and the compatibility properties of `f` implies that
`f.toFun' S[X] m = ∑ (f.multiComponent n).toFun' S m`.
-/

open LinearMap TensorProduct

noncomputable section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] {σ : Type*}

variable {p q : MvPolynomial σ R} (f : R →+* S) (x : σ → S)

theorem eval₂_mul_eq_zero_of_left (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  simp [eval₂_mul f x, hp]

theorem eval₂_mul_eq_zero_of_right (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

@[simp]
theorem eval₂_X_pow {s : σ} {n : ℕ} : ((X s) ^ n).eval₂ f x = (x s) ^ n := by
  rw [X_pow_eq_monomial]
  convert eval₂_monomial f x
  simp

variable [Algebra R S] {S' : Type*} [CommSemiring S'] [Algebra R S']

lemma C_eq_algebraMap' (r : R) :
    C (algebraMap R S r) = algebraMap R (MvPolynomial σ S) r := rfl

/-- baseChange φ aplies φ on the coefficients of a polynomial in `(MvPolynomial σ S)`. -/
noncomputable def baseChange (φ : S →ₐ[R] S') : MvPolynomial σ S →ₐ[R] MvPolynomial σ S' where
  toRingHom := eval₂Hom (C.comp φ) X
  commutes' := fun r ↦ by simp

lemma coeff_baseChange_apply (φ : S →ₐ[R] S') (f : MvPolynomial σ S) (n : σ →₀ ℕ) :
    coeff n (baseChange φ f) = φ (coeff n f) := by
  classical
  rw [baseChange, AlgHom.coe_mk, coe_eval₂Hom]
  induction f using MvPolynomial.induction_on generalizing n with
  | C r =>
    simp only [eval₂_C, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, coeff_C,
      apply_ite φ, map_zero]
  | add f g hf hg => simp only [eval₂_add, coeff_add, hf, hg, map_add]
  | mul_X q s h =>
    simp only [eval₂_mul, eval₂_X, coeff_mul, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [h k.1, coeff_X', MonoidWithZeroHom.map_ite_one_zero]

lemma lcoeff_comp_baseChange_eq (φ : S →ₐ[R] S') (p : σ →₀ ℕ) :
    LinearMap.comp (AlgHom.toLinearMap φ) ((lcoeff S p).restrictScalars R) =
      LinearMap.comp ((lcoeff S' p).restrictScalars R) (baseChange φ).toLinearMap := by
  ext f
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, lcoeff_apply,
    AlgHom.toLinearMap_apply, coeff_baseChange_apply]

lemma baseChange_monomial (φ : S →ₐ[R] S') (n : σ →₀ ℕ) (a : S) :
    (baseChange φ) ((MvPolynomial.monomial n) a) = (MvPolynomial.monomial n) (φ a) := by
  simp only [baseChange, AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply]
  rw [monomial_eq]

theorem baseChange_comp_monomial_eq (φ : S →ₐ[R] S') (n : σ →₀ ℕ) :
    (MvPolynomial.baseChange φ).toLinearMap ∘ₗ ((monomial n).restrictScalars R) =
      ((monomial n).restrictScalars R) ∘ₗ φ.toLinearMap := by
  ext
  simp only [coe_comp, coe_restrictScalars, Function.comp_apply,
    AlgHom.toLinearMap_apply, baseChange_monomial]

theorem foo [DecidableEq σ] {M : σ → Type*} [(i : σ) → AddCommMonoid (M i)] [(i : σ) → Module R (M i)]
  (φ : S →ₐ[R] S') (s : S) (m : (i : σ) → M i) (i : σ) :
  ((MvPolynomial.baseChange φ).toLinearMap ∘ₗ scalarRTensorAlgEquiv.toLinearMap) (X i ⊗ₜ[R] s) ⊗ₜ[R] Pi.single i (m i) =
    scalarRTensorAlgEquiv (X i ⊗ₜ[R] φ s) ⊗ₜ[R] Pi.single i (m i) := by
  simp only [baseChange, eval₂Hom_eq_bind₂, coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply, AlgHom.coe_mk, ← bind₂_map, bind₂_C_left,
    RingHomCompTriple.comp_apply]
  congr
  simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  ext d
  simp [rTensorAlgEquiv_apply, coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, Algebra.TensorProduct.lid_tmul, map_smul]

open Finsupp

theorem sum_add_index {ι R A M : Type*} [DecidableEq ι] [Semiring R] [CommSemiring A] [AddCommMonoid M] [Module R A]
    [Module R M] {p q : MvPolynomial ι A} {f : (ι →₀ ℕ) → A → M}
    (hf : ∀ i ∈ p.support ∪ q.support, f i 0 = 0)
    (h_add : ∀ i ∈ p.support ∪ q.support, ∀ (b₁ b₂ : A), f i (b₁ + b₂) = f i b₁ + f i b₂) :
    (p + q).sum f = p.sum f + q.sum f :=
 Finsupp.sum_add_index hf h_add

theorem sum_eq_of_subset {ι R A M : Type*} [Semiring R] [CommSemiring A] [AddCommMonoid M]
    [Module R A] [Module R M] {p : MvPolynomial ι A} (f : (ι →₀ ℕ) → A → M)
    (hf : ∀ (i : ι →₀ ℕ), f i 0 = 0) {s : Finset (ι →₀ ℕ) } (hs : p.support ⊆ s) :
    p.sum f = ∑ n ∈ s, f n (p.coeff n) :=
  Finsupp.sum_of_support_subset _ hs f (fun i _ ↦ hf i)

--@[simps]
def lsum {ι R A M : Type*} [Semiring R] [CommSemiring A] [AddCommMonoid M] [Module R A] [Module R M]
    (f : (ι →₀ ℕ) → A →ₗ[R] M) : MvPolynomial ι A →ₗ[R] M where
  toFun p := p.sum (f · ·)
  map_add' p q := by
    classical
    apply MvPolynomial.sum_add_index (R := R) (fun n _ => (f n).map_zero)
      (fun n _ _ _ => (f n).map_add _ _)
  map_smul' c p := by
    rw [sum_eq_of_subset (R := R) (f · ·) (fun n => (f n).map_zero) support_smul]
    simp [sum_def, Finset.smul_sum, coeff_smul, RingHom.id_apply]

@[simp]
theorem lsum_apply {ι R A M : Type*} [Semiring R] [CommSemiring A]
    [AddCommMonoid M] [Module R A] [Module R M] (f : (ι →₀ ℕ) → A →ₗ[R] M) (p : MvPolynomial ι A) :
    (lsum f) p = p.sum fun (x1 : ι →₀ ℕ) (x2 : A) => (f x1) x2 := rfl

theorem rTensor'_sum [DecidableEq σ] {N : Type*} [AddCommMonoid N] [Module R N]
    (φ : (σ →₀ ℕ) → S) (sXn : (MvPolynomial σ S) ⊗[R] N) :
    (rTensor (R := R) (N := N) (S := S) sXn).sum (fun p sn ↦ (φ p) • sn) =
      (lsum (fun n ↦ (LinearMap.lsmul S S (φ n)).restrictScalars R)).rTensor N sXn := by
  induction sXn using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.sum_zero_index]
  | tmul p n =>
    induction p using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [add_tmul, LinearEquiv.map_add]
      rw [Finsupp.sum_add_index, hp, hq, LinearMap.map_add]
      · intro x _; apply smul_zero
      · intro x _; apply smul_add
    | monomial p s =>
      rw [Finsupp.sum_eq_single p, rTensor_apply, rTensor_tmul]
      simp only [coe_restrictScalars, lcoeff_apply, coeff_monomial, ↓reduceIte, rTensor_tmul,
          MvPolynomial.lsum_apply, lsmul_apply, smul_eq_mul, mul_zero, sum_monomial_eq,
          smul_tmul', smul_eq_mul]
      · intro b _ hb
        simp only [rTensor_apply, rTensor_tmul, coe_restrictScalars, lcoeff_apply, coeff_monomial]
        rw [if_neg (Ne.symm hb)]
        simp only [zero_tmul, smul_zero]
      · exact fun _ ↦ smul_zero _
  | add p q hp hq =>
    rw [LinearEquiv.map_add, Finsupp.sum_add_index (fun x _ ↦ smul_zero _) (fun x _ ↦ smul_add _),
      hp, hq, LinearMap.map_add]

end MvPolynomial

namespace PolynomialLaw

open PolynomialLaw

section MultiHomogeneous

section

open Finsupp MvPolynomial

-- **MI**: I replaced  `CommRing R` by `CommSemiring R`.
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

-- **MI**: I replaced  `CommRing S` by `CommSemiring S`.
-- TODO: fix docstring
/-- A polynomial map `f : Π (i : ι), M i →ₚ[R] N` is multihomogeneous of multidegree `n : ι →₀ ℕ`
  if for all families `{z_i : R ⊗ M i}_{i : ι}`, `{r_i : R}_{i : ι}`, one has
  `f (r_1 • z_1, r_2 • z_2, ...) = Π i r_i^(n i) • f (z_1, z_2, ...)`. -/
def IsMultiHomogeneousOfDegree (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) : Prop :=
  ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : ι → S) (m : S ⊗ ((i : ι) → M i)),
    f.toFun' S ((piRight R S S M).symm fun i ↦ r i • (piRight R R S M) m i) =
      (∏ i, r i ^ n i) • f.toFun' S m

  /- ∀ (S : Type u) [CommSemiring S] [Algebra R S] (r : ι → S) (m : (i : ι) → S ⊗[R] M i),
    f.toFun' S ((TensorProduct.piRight R S _ _).symm fun i ↦ r i • m i) =
      (∏ i, (r i)^(n i)) • f.toFun' S ((TensorProduct.piRight R R _ _).symm m) -/

example (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N)
    (hf : IsMultiHomogeneousOfDegree n f)
    (S : Type u) [CommSemiring S] [Algebra R S]
    (r : ι → S) (m : (i : ι) → (S ⊗ M i)) :
    f.toFun' S ((TensorProduct.piRight R S _ _).symm fun i ↦ r i • m i) =
      (∏ i, (r i)^(n i)) • f.toFun' S ((TensorProduct.piRight R R _ _).symm m)  := by
  unfold IsMultiHomogeneousOfDegree at hf
  specialize hf _ r ((TensorProduct.piRight R R S M).symm m)
  rwa [LinearEquiv.apply_symm_apply] at hf

theorem IsMultiHomogeneousOfDegree_add (n : ι →₀ ℕ) {f g : PolynomialLaw R (Π i, M i) N}
    (hf : f.IsMultiHomogeneousOfDegree n) (hg : g.IsMultiHomogeneousOfDegree n) :
    (f + g).IsMultiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp only [add_def_apply, smul_add, hf S s m, hg S s m]

theorem IsMultiHomogeneousOfDegree_smul (n : ι →₀ ℕ) (r : R) {f : PolynomialLaw R (Π i, M i) N}
    (hf : f.IsMultiHomogeneousOfDegree n) :
    (r • f).IsMultiHomogeneousOfDegree n := fun S _ _ s m ↦ by
  simp only [smul_def, Pi.smul_apply, hf S]
  exact smul_comm _ _ _

/-- The submodule of homogeneous polynomial laws of degree `p`. -/
def multiGrade (n : ι →₀ ℕ) : Submodule R (PolynomialLaw R (Π i, M i) N) where
  carrier            := IsMultiHomogeneousOfDegree n
  add_mem' hf hg     := IsMultiHomogeneousOfDegree_add n hf hg
  smul_mem' r f hf   := IsMultiHomogeneousOfDegree_smul n r hf
  zero_mem' S _ _ r _:= by simp only [zero_def, Pi.zero_apply, smul_zero]

lemma mem_multiGrade (f : PolynomialLaw R (Π i, M i) N) (n : ι →₀ ℕ) :
    f ∈ multiGrade n ↔ IsMultiHomogeneousOfDegree n f := by rfl

lemma piRightHom_rTensor_eq_rTensor_piRightHom
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]
    (ψ : N →ₗ[R] P)
    (m : N ⊗[R] ((i : ι) → M i)) (i : ι) :
    (piRightHom R S P M) ((LinearMap.rTensor ((i : ι) → M i) ψ) m) i = LinearMap.rTensor (M i) ψ (piRightHom R S N M m i) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply] at hx hy ⊢
    rw [hx, hy]
  | tmul t m => simp

lemma piRight_rTensor_eq_rTensor_piRight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {N : Type*} [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
    {P : Type*} [AddCommMonoid P] [Module R P] [Module S P] [IsScalarTower R S P]
    (ψ : N →ₗ[R] P)
    (m : N ⊗[R] ((i : ι) → M i)) :
    (piRight R S P M) ((LinearMap.rTensor ((i : ι) → M i) ψ) m) =
      fun i ↦ LinearMap.rTensor (M i) ψ (piRight R S N M m i) := by
  ext i
  simp [piRightHom_rTensor_eq_rTensor_piRightHom]

@[simp]
lemma coe_piRightHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N] :
    ⇑(piRightHom R S N M) = (piRightHom R R N M) :=
  rfl

@[simp]
lemma coe_piRight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N] :
    ⇑(piRight R S N M) = (piRight R R N M) :=
  rfl

@[simp]
lemma coe_piRight_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N] :
    ⇑(piRight R S N M).symm = (piRight R R N M).symm := by
  ext d
  simp only [LinearEquiv.symm_apply_eq, coe_piRight]
  simp only [LinearEquiv.apply_symm_apply]

-- I tried to avoid the next one, but with no success
lemma piRight_rTensor_eq_rTensor_piRight'
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommSemiring R]
    {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
    {S : Type*} [CommSemiring S] [Algebra R S]
    {T : Type*} [CommSemiring T] [Algebra R T]
    (ψ : T →ₐ[R] S)
    (m : T ⊗[R] ((i : ι) → M i)) (i : ι) :
    (piRight R S S M) ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap) m) i = LinearMap.rTensor (M i) ψ.toLinearMap (piRight R T T M m i) := by
  simp [piRightHom_rTensor_eq_rTensor_piRightHom]

-- TODO: generalize, speed up
theorem isMultiHomogeneousOfDegree_toFun'.extracted_1_4 (d : ℕ)
    (m' : MvPolynomial (Fin d) R ⊗[R] ((i : ι) → M i))
    (r' : ι → (MvPolynomial (Fin d) R)) (i : ι) :
    r' i • (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M) m' i =
      (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M)
        ((piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M).symm fun i ↦
          r' i • (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M) m' i)
        i := by
  rw [← Pi.smul_apply]
  rw [← map_smul]
  induction m' using TensorProduct.induction_on with
  | zero =>
    simp only [smul_zero, map_zero, Pi.zero_apply]
    have h : (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M)
      ((piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M).symm fun i ↦ 0) = 0 := by
      calc (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M)
              ((piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M).symm fun i ↦ 0)
        _ = (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M)
              ((piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M).symm 0)  := by
          congr
        _ = 0 := by simp only [map_zero]
    rw [h, Pi.zero_apply]
  | add x y hx hy =>
    simp only [smul_add, hx, hy, map_add, Pi.add_apply, coe_piRight_symm]
    have : (fun i ↦
      r' i • (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M) x i + r' i •
      (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M) y i) =
      (fun i ↦
      r' i • (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M) x i) + fun i ↦ r' i •
       (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M) y i := rfl
    simp_rw [this]
    simp only [map_add, Pi.add_apply]
  | tmul p m =>
    simp only [map_smul, piRight_apply, piRightHom_tmul, Pi.smul_apply, coe_piRight_symm,
      coe_piRightHom]
    rw [← piRight_apply]
    have : r' i • p ⊗ₜ[R] m i = (piRight R (MvPolynomial (Fin d) R) (MvPolynomial (Fin d) R) M)
        (r' i • p ⊗ₜ[R] Pi.single i (m i)) i := by
      simp only [map_smul, piRight_apply, piRightHom_tmul, Pi.smul_apply, Pi.single_eq_same]
    rw [this]
    simp only [map_smul, piRight_apply, piRightHom_tmul, Pi.smul_apply, Pi.single_eq_same,
      LinearEquiv.apply_symm_apply]

/-- If `f` is multihomogeneous of multidegree `n`, then all `f.toFun S` are multihomogeneous of
  multidegree `n`. -/
lemma isMultiHomogeneousOfDegree_toFun {n : ι →₀ ℕ} {f : PolynomialLaw R (Π i, M i) N}
    (hf : IsMultiHomogeneousOfDegree n f) (S : Type*) [CommSemiring S] [Algebra R S] (r : ι → S)
    (m : S ⊗[R] (Π i, M i)) :
    f.toFun S ((TensorProduct.piRight R S _ _).symm
      (fun i ↦ r i • ((TensorProduct.piRight R S _ _ ) m) i)) =
      (∏ i, (r i)^(n i)) • f.toFun S m := by
  choose d ψ m' r' hm' hr' using PolynomialLaw.exists_lift'' m r
  simp only [← hr', ← hm', ← map_pow, ← map_prod, ←
    isCompat_apply, toFun_eq_toFun', smul_rTensor]
  rw [← hf, ← toFun_eq_toFun', isCompat_apply]
  apply congr_arg
  rw [LinearEquiv.symm_apply_eq]
  ext i
  simp only [piRight_rTensor_eq_rTensor_piRight', smul_rTensor]
  congr
  exact isMultiHomogeneousOfDegree_toFun'.extracted_1_4 d m' r' i

/-- If `f` is multihomogeneous of multidegree `n`, then `f.ground` is too.  -/
lemma isMultiHomogeneousOfDegree_ground {n : ι →₀ ℕ} {f : PolynomialLaw R (Π i, M i) N}
    (hf : IsMultiHomogeneousOfDegree n f) (r : ι → R) (m : (Π i, M i)) :
    f.ground (r • m) = (∏ i, (r i)^(n i)) • f.ground m := by
  have hfrm := hf R r ((TensorProduct.lid R (Π i, M i)).symm m)
  simp only [lid_symm_apply, piRight_apply, piRightHom_tmul] at hfrm
  simp only [ground, Function.comp_apply, lid_symm_apply]
  rw [← map_smul, ← hfrm]
  congr
  simp only [← tmul_smul, piRight_symm_apply]
  rfl

theorem IsMultiHomogeneousOfDegree.comp {P : Type*} [AddCommMonoid P] [Module R P]
    {f : (Π i, M i) →ₚₗ[R] N} {g : N →ₚₗ[R] P} {p : ι →₀ ℕ} {q : ℕ}
    (hf : f.IsMultiHomogeneousOfDegree p) (hg : g.IsHomogeneousOfDegree q) :
    (g.comp f).IsMultiHomogeneousOfDegree (q • p) := by
  intro S _ _ r m
  have hf' := hf S r m/- hf S r m, hg S, -/
  simp only [piRight_apply, coe_piRightHom] at hf'
  have hg' := hg S
  simp only [piRight_apply, comp_toFun', Function.comp_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_comm q, pow_mul, Finset.prod_pow, Pi.smul_apply, hf', hg']

/-- The coefficients of a homogeneous polynomial map of degree `p` vanish outside of degree `p`. -/
lemma isMultiHomogeneousOfDegree_multiCoeff {n : ι →₀ ℕ} {f : PolynomialLaw R (Π i, M i) N}
    (hf : IsMultiHomogeneousOfDegree n f) (m : Π i, M i) (d : ι →₀ ℕ) (hd : d ≠ n) :
    PolynomialLaw.multiCoeff m f d = 0 := by
  classical
  let e (b : ι →₀ ℕ) (k : ℕ) : Option ι →₀ ℕ :=
    Finsupp.update (Finsupp.mapDomainEmbedding (Function.Embedding.some) b) none k
  have he : ∀ b k, (X none ^ k * (Finset.prod Finset.univ
      fun x => X (some x) ^ b x) : MvPolynomial (Option ι) R) = monomial (e b k) 1 := fun b k ↦ by
    simp only [Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply, monomial_eq,
      map_one, Finsupp.prod_pow, Finsupp.coe_update, Fintype.prod_option, Function.update_self,
      ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, one_mul, e]
    exact congr_arg₂ _ rfl (Finset.prod_congr rfl (fun _ _ => by
      rw [Finsupp.mapDomain_apply (Option.some_injective ι)]))
  have he_some : ∀ b k i, e b k (some i) = b i := fun b k i ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, reduceCtorEq, ↓reduceDIte,
      Finsupp.mapDomain_apply (Option.some_injective ι), e]
  have he_none : ∀ b k, k = e b k none := fun b k ↦ by
    simp only [Finsupp.update, Finsupp.mapDomainEmbedding_apply, Function.Embedding.some_apply,
      Finsupp.coe_mk, Function.update, ↓reduceDIte, e]
   /-  On écrit l'homogénéité : f (∑ T ⬝ X_i m_i) = T ^ p ⬝ f(∑ X_i m_i)
   ∑ coeff f e (T X) ^ e = T ^ p ⬝ ∑ coeff f e X ^ e
   Identification : (coeff f e) T^|e| X^ e = coeff f e T ^ p X ^ e
   On en déduit coeff f e = 0 si |e| ≠ p .    -/
  let μ : MvPolynomial (Option ι) R ⊗[R] (Π i, M i) :=
    Finset.univ.sum (fun i => X (some i) ⊗ₜ[R] m)
  have hf' := isMultiHomogeneousOfDegree_toFun hf (MvPolynomial (Option ι) R) (fun i ↦ X none) μ
  simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply, Finset.smul_sum, smul_tmul',
    smul_eq_mul, coe_piRight_symm, μ] at hf'
  let φ : MvPolynomial (Option ι) R ⊗[R] N →ₗ[R] N :=
    (TensorProduct.lid R N).toLinearMap.comp
      (LinearMap.rTensor N (lcoeff R (e d (d.sum fun _ n => n))))
  let hφ := LinearMap.congr_arg (f := φ) hf'
  simp only [Finset.prod_pow_eq_pow_sum] at hφ
  /- simp only [map_finsuppSum, LinearMap.map_smul, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum] at hφ -/
  sorry/- rw [Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true]),
    Finsupp.sum_eq_single d _ (by simp only [tmul_zero, map_zero, implies_true])] at hφ
  simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
    AddHom.coe_mk, lid_tmul, φ] at hφ
  rw [he, coeff_monomial, if_pos, _root_.one_smul, he, coeff_monomial, if_neg, _root_.zero_smul]
    at hφ
  exact hφ
  · intro hd'
    apply hd
    convert (DFunLike.ext_iff.mp hd'.symm) none <;> exact (he_none _ _)
  · simp only [Finset.mem_univ, forall_true_left, implies_true,
      Finsupp.sum_of_support_subset _ (Finset.subset_univ d.support)]
  all_goals
  · intro b _ hb'
    simp only [lcoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, rTensor_tmul, coe_mk,
      AddHom.coe_mk, lid_tmul, φ]
    rw [he, coeff_monomial, if_neg, _root_.zero_smul]
    intro h
    apply hb'
    ext i
    rw [← he_some b _ i, h]
    exact he_some d _ i  -/

/-- A polynomial map `f` is homogeneous of degree `p` iff all of its coefficients
  `PolynomialLaw.coeff m f` vanish outside of degree `p`, for all `m : Fin n → M`. -/
theorem isMultiHomogeneousOfDegree_of_coeff_iff (p : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    IsMultiHomogeneousOfDegree p f ↔ ∀ (m : Π i, M i)  (n : ι →₀ ℕ) (_ : n ≠ p),
      PolynomialLaw.multiCoeff m f n = 0 := by
  refine ⟨fun hf m n hn ↦ isMultiHomogeneousOfDegree_multiCoeff hf m n hn, fun H S _ _ r μ => ?_⟩
  obtain ⟨n, s, m, rfl⟩ := TensorProduct.exists_Fin S μ
  have (i : ι) : r i • (piRight R R S M) (∑ i, s i ⊗ₜ[R] m i) i =
      (piRight R R S M) (∑ j, (r i • s j) ⊗ₜ[R] m j) i := by
    simp only [map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply,
      Finset.smul_sum, TensorProduct.smul_tmul']
  simp_rw [this]
  simp_rw [coe_piRight_symm,/-  LinearEquiv.symm_apply_apply -/]
  simp only [smul_eq_mul, map_sum, piRight_apply, piRightHom_tmul, Finset.sum_apply]
  rw [← toFun_eq_toFun',toFun_sum_tmul_eq_coeff_sum, Finsupp.smul_sum]
  sorry


theorem isMultiHomogeneousOfMultiDegreeOne_coeff {f : PolynomialLaw R (Π i, M i) N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) {d : ι →₀ ℕ}
    (hd : d ≠ Finsupp.single i 1) : (multiCoeff m f) d = 0 :=
  isMultiHomogeneousOfDegree_multiCoeff hf m d hd


theorem isMultiHomogeneousOfDegreeOne_coeff_support_le {f : PolynomialLaw R (Π i, M i) N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f).support ⊆ Finset.map
      ⟨fun i ↦ Finsupp.single i 1, Finsupp.single_left_injective (by norm_num)⟩ Finset.univ := by
  intro d hd
  simp only [Finsupp.mem_support_iff, ne_eq] at hd
  simp only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
    true_and]
  exact ⟨i, ((not_imp_comm.mp (isMultiHomogeneousOfMultiDegreeOne_coeff i hf m)) hd).symm⟩

theorem _root_.MvPolynomial.prod_X_pow_eq_monomial' {R : Type u} {σ : Type u_1} [Fintype σ]
    {s : σ →₀ ℕ} [CommSemiring R] : ∏ x, X (R := R) x ^ s x = (monomial s) 1 := sorry

theorem isMultiHomogeneousOfMultiDegreeOne_coeff_single {f : PolynomialLaw R (Π i, M i) N} (i : ι)
    (hf : f.IsMultiHomogeneousOfDegree (Finsupp.single i 1)) (m : Π i, M i) :
    (multiCoeff m f) (Finsupp.single i 1) = f.ground (Pi.single i (m i)) := by
  classical
  simp only [ground, Function.comp_apply, TensorProduct.lid_symm_apply, ← toFun_eq_toFun']
  simp only [multiCoeff, multiGenerize, coe_comp, LinearEquiv.coe_coe, coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  --simp only [scalarRTensor_apply, EmbeddingLike.apply_eq_iff_eq]
  simp only [toFun_sum_tmul_eq_multiCoeff_sum]
  simp only [map_finsuppSum, Finsupp.sum_apply, scalarRTensor_apply, rTensor_tmul, lcoeff_apply,
    lid_tmul]
  let r : ι → R := Function.const ι 1
  have : (1 : R) = (Function.const ι 1) i := rfl
  rw [this, toFun_tmul_eq_multiCoeff_sum]
  simp only [Finsupp.sum, Function.const_apply, one_pow, map_sum, lid_tmul, _root_.one_smul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [isMultiHomogeneousOfDegree_of_coeff_iff] at hf
  --simp? [coeff_single_X_pow]
  have hd' : d = Finsupp.single i 1 := sorry
  simp only [hd']
  rw [MvPolynomial.prod_X_pow_eq_monomial']
  simp only [coeff_monomial, ↓reduceIte, _root_.one_smul]

end

section Components

-- I need `ι : Type u` to be able to apply `f.toFun'`.
-- Update: I changed to `ι : Type*` and using `toFun`.
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type u} [CommSemiring R]

variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]

open MvPolynomial

variable {S : Type*} [CommSemiring S] [Algebra R S]

variable (ι R S M)

noncomputable def el_S_hom : (S ⊗[R] Π i, M i) →ₗ[R] MvPolynomial ι R ⊗[R] (S ⊗[R] (Π i, M i)) where
  toFun := fun m ↦ ∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
    (Pi.single (M := fun i ↦  S ⊗[R] M i) i (TensorProduct.piRight R R S _ m i))
  map_add' m m'  := by
    simp only [piRight_apply, map_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← TensorProduct.tmul_add]
    congr
    simp only [Pi.single_add, map_add]
  map_smul' r m := by
    simp only [map_smul, piRight_apply, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← tmul_smul, Pi.single_smul, map_smul]

noncomputable def el_S'_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι R ⊗[R] S) ⊗[R] (Π i, M i) :=
  (TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm.comp (el_S_hom ι R M S)

noncomputable def el_S''_hom : (S ⊗[R] Π i, M i) →ₗ[R] (MvPolynomial ι S) ⊗[R] (Π i, M i) :=
  (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv).comp (el_S'_hom ι R M S)

variable {ι R M S}

noncomputable def multiGenerize_S (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    MvPolynomial ι S ⊗[R] N := f.toFun (MvPolynomial ι S) (el_S''_hom ι R M S m)

noncomputable def multiCoeff_S (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N)
    (n : ι →₀ ℕ) : S ⊗[R] N := MvPolynomial.rTensor (multiGenerize_S m f) n

lemma multiCoeff_S_apply (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) (n : ι →₀ ℕ) :
  multiCoeff_S m f n = MvPolynomial.rTensor (f.toFun (MvPolynomial ι S)
    (LinearEquiv.rTensor (Π i, M i) scalarRTensorAlgEquiv.toLinearEquiv
    ((TensorProduct.assoc R (MvPolynomial ι R) S (Π i, M i)).symm
    (∑ (i : ι), (X i) ⊗ₜ (TensorProduct.piRight R R S _).symm
    (Pi.single (M := fun i ↦  S ⊗[R] M i) i (TensorProduct.piRight R R S _ m i)))))) n := rfl

variable (s : Π (_ : ι), S) (m : Π i, M i)

lemma multiCoeff_S_apply_smul_tmul (s : Π i, S) (t : S) (m : Π i, M i)
    (f : PolynomialLaw R (Π i, M i) N) (n : ι →₀ ℕ) :
    multiCoeff_S ((TensorProduct.piRight R R S _).symm (fun i ↦ ((s i) * t) ⊗ₜ[R] (m i))) f n =
      (∏ i, (s i) ^ n i) •
        multiCoeff_S ((TensorProduct.piRight R R S _).symm (fun i ↦ t ⊗ₜ[R] (m i))) f n  := by
  simp only [multiCoeff_S_apply, LinearEquiv.apply_symm_apply, piRight_symm_single, map_sum,
    assoc_symm_tmul, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, piRight_symm_apply,
    piRight_apply, piRightHom_tmul]
  simp only [toFun_sum_tmul_eq_multiCoeff_sum]
  simp only [rTensor_apply]
  simp only [Finsupp.sum, map_sum, rTensor_tmul, coe_restrictScalars, lcoeff_apply]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [smul_tmul']
  congr
  rw [← MvPolynomial.coeff_smul]
  -- TODO: lemma
  have (i : ι) : scalarRTensorAlgEquiv (X (R := R) i ⊗ₜ[R] t) =
      t • X (R := S) i := by
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    ext e
    simp only [coeff_smul]

    simp only [coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_coe,
      Algebra.TensorProduct.lid_tmul, smul_eq_mul]
    simp only [coeff_X', ite_smul, _root_.one_smul, _root_.zero_smul, mul_ite, mul_one, mul_zero]
  have that (i : ι) : scalarRTensorAlgEquiv (X (R := R) i ⊗ₜ[R] (s i * t)) =
      (s i * t) • X (R := S) i := by
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    ext e
    simp only [coeff_smul]

    simp only [coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_coe,
      Algebra.TensorProduct.lid_tmul, smul_eq_mul]
    simp only [coeff_X', ite_smul, _root_.one_smul, _root_.zero_smul, mul_ite, mul_one, mul_zero]
  have foo : ((∏ i, s i ^ d i) • ∏ i, scalarRTensorAlgEquiv (X i ⊗ₜ[R] t) ^ d i) =
      (∏ i, (s i ^ d i)  • scalarRTensorAlgEquiv (X i ⊗ₜ[R] t) ^ d i) := by
    simp_rw [this]
    --rw [← Finset.prod_mul_distrib]
    sorry
  by_cases hnd : n = d
  · simp only [hnd]
    rw [foo]
    congr
    ext j p
    rw [← smul_pow]
    congr
    simp_rw [this, that]
    rw [← smul_eq_mul]
    rw [smul_assoc]

  · have h0 : (0 : S) = 0 := rfl
    simp_rw [this, that]
    convert h0
    · simp [smul_eq_C_mul, mul_pow]
      simp_rw [← C_pow, ← C_mul]
      have hd := monomial_eq (s := d) (R := S)
       (a := (∏ x, (s x ^ d x * t ^ d x)))
      /- simp only [map_prod, C_mul, C_pow, Finsupp.prod,
        prod_X_pow_eq_monomial] at hd -/

      calc MvPolynomial.coeff n (∏ x, C (s x ^ d x * t ^ d x) * X x ^ d x)
        _ = MvPolynomial.coeff n (( C (∏ x, s x ^ d x * t ^ d x)) * (∏ x, X x ^ d x)) := sorry
        _ = MvPolynomial.coeff n (( C (∏ x, s x ^ d x * t ^ d x)) * (d.prod fun n e ↦ X n ^ e)) := sorry
        _ = MvPolynomial.coeff n ((monomial d) (∏ x, s x ^ d x * t ^ d x)) := by rw [hd]
        _ = 0 := by
          rw [coeff_monomial, if_neg (Ne.symm hnd)]

    sorry

lemma multiCoeff_S_apply_smul (s : Π i, S) (sm : S ⊗[R] Π i, M i)
    (f : PolynomialLaw R (Π i, M i) N) (n : ι →₀ ℕ) :
    multiCoeff_S ((TensorProduct.piRight R R S _).symm
      (fun i ↦ (s i) • ((TensorProduct.piRight R R S _) sm i))) f n =
      (∏ i, (s i) ^ n i) • multiCoeff_S (sm) f n  := by
  let ψ := ((aeval (R := S) (fun i ↦ (C (s i) * X i : MvPolynomial ι S))).restrictScalars R)


  suffices ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (∑ i,
              X i ⊗ₜ[R]
                (piRight R R S M).symm
                  (Pi.single i ((piRight R R S M)
                   ((piRight R R S M).symm fun i ↦ s i • (piRight R R S M) sm i) i)))))
                   =
    ((LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap)
      ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (∑ i,
              X i ⊗ₜ[R]
                (piRight R R S M).symm
                  (Pi.single i ((piRight R S S M) sm i)))))) by
    simp only [multiCoeff_S_apply,]
    simp_rw [this, ← f.isCompat_apply]
    clear this
    simp only [← coe_piRight R S]
    generalize  ht : (f.toFun (MvPolynomial ι S)
          ((LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
            ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
              (∑ i, X i ⊗ₜ[R] (piRight R R S M).symm (Pi.single i ((piRight R S S M) sm i)))))) = t

    rw [rTensor_apply, rTensor_apply, ← rTensor_comp_apply]
    conv_rhs =>
      rw [← (IsLinearMap.isLinearMap_smul (∏ i, s i ^ n i)).mk'_apply, ← coe_restrictScalars R,
        ← LinearMap.comp_apply]
    apply LinearMap.congr_fun
    apply symm
    dsimp only [LinearMap.rTensor, TensorProduct.map]
    apply TensorProduct.lift.unique
    intro f k
    simp only [compl₂_id, coe_comp, coe_restrictScalars, Function.comp_apply, lift.tmul,
      lcoeff_apply, mk_apply, IsLinearMap.mk'_apply, AlgHom.toLinearMap_apply,
      TensorProduct.smul_tmul']
    apply congr_arg₂ _ _ rfl
    -- ψ f = f (s • X)
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg => rw [coeff_add, smul_add, hf, hg, ← coeff_add, map_add]
    | monomial k' a =>
        simp only [ψ, coeff_monomial]
        split_ifs with h
        · rw [smul_eq_mul, mul_comm, h, AlgHom.coe_restrictScalars', aeval_monomial,
           algebraMap_eq
            /- monomial_pow,
            one_mul, ← C_eq_algebraMap -/]
          rw [coeff_C_mul]
          simp only [Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib]
          simp_rw [← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_pos rfl]
          simp
        · simp only [smul_zero, AlgHom.coe_restrictScalars', aeval_monomial, algebraMap_eq]
          rw [coeff_C_mul]
          simp only [Finsupp.prod_pow]
          simp_rw [mul_pow, Finset.prod_mul_distrib]
          simp_rw [← C_pow, ← map_prod]
          rw [coeff_C_mul, prod_X_pow_eq_monomial', coeff_monomial, if_neg h]
          simp
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (LinearMap.rTensor ((i : ι) → M i) ψ.toLinearMap)
    ((LinearMap.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv.toLinearMap)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X i ⊗ₜ[R]
          (piRight R R S M).symm
            (Pi.single i ((piRightHom R S S M) sm i)))))

  simp only [AlgEquiv.toLinearEquiv_toLinearMap, ← rTensor_comp_apply]
  simp only [LinearEquiv.apply_symm_apply]

  induction sm using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero, Pi.ofNat_apply, smul_zero, Pi.single_zero,
      tmul_zero]
  | tmul t m =>
    have hi (i : ι) : s i • (piRight R S S M) (t ⊗ₜ[R] m) i =
       (piRight R R S M) ((s i * t) ⊗ₜ[R] m) i := by
      simp [smul_tmul']
    rw [← coe_piRight R S]
    simp_rw [hi]
    simp only [piRight_apply, piRightHom_tmul, piRight_symm_single,
      assoc_symm_tmul, LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, rTensor_tmul,
      coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply]

    simp only [AlgHom.coe_restrictScalars', ψ]
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      ]
    congr
    simp only [rTensorAlgHom_apply_eq, rTensor_apply_tmul]
    simp only [Finsupp.sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X i) := rfl
    have hR : Nontrivial R := sorry
    simp only [this, support_X, Finset.mem_singleton] at hd
    simp only [hd]
    simp only [MvPolynomial.aeval_def]
    simp only [mapAlgEquiv_apply, algebraMap_eq, eval₂_map]
    simp only [eval₂, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, Finsupp.prod_pow,
      map_zero, zero_mul, Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]

    simp only [X, ← single_eq_monomial, Finsupp.single_eq_same, _root_.one_smul]

    rw [Finset.prod_eq_single i]
    simp only [Finsupp.single_eq_same, pow_one]
    simp only [single_eq_monomial, map_monomial, RingHom.coe_coe, Algebra.TensorProduct.lid_tmul,
      _root_.one_smul]
    simp only [mul_comm (s i) t, C_mul_monomial, mul_one]

    · intro j _ hj
      rw [Finsupp.single_eq_of_ne (Ne.symm hj), pow_zero]
    · intro hj
      exact absurd (Finset.mem_univ _) hj

  | add sm sm' h h' =>
    simp only [map_add, Pi.add_apply, smul_add]
    simp only [Pi.single_add, map_add, tmul_add, h, h']

lemma multiCoeff_S_def (m : S ⊗[R] Π i, M i) (f : PolynomialLaw R (Π i, M i) N) :
    multiCoeff_S m f = (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))) := by
  ext n
  simp only [multiCoeff_S_apply, piRight_apply, map_sum]

/- Here we define the multihomogeneous components of a `PolynomialLaw`
 and show how it recomposes as its locally finite sum -/

-- **MI**: this proof is really slow.
theorem bar (n : ι →₀ ℕ) (f : ((i : ι) → M i) →ₚₗ[R] N) {S' : Type*} [CommSemiring S']
    [Algebra R S'] (φ : S →ₐ[R] S')
    (sm : S ⊗[R] ((i : ι) → M i)) :
    (LinearMap.rTensor N φ.toLinearMap) (multiCoeff_S sm f n) =
    multiCoeff_S ((LinearMap.rTensor ((i : ι) → M i) φ.toLinearMap) sm) f n := by
  simp only [multiCoeff_S_def, rTensor_apply, ← rTensor_comp_apply]
  rw [lcoeff_comp_baseChange_eq, rTensor_comp_apply, f.isCompat_apply, map_sum]
  congr 3
  ext i
  induction sm using TensorProduct.induction_on with
  | zero => simp [map_zero, Pi.single_zero, tmul_zero]
  | tmul s m =>
      simp only [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul, rTensor_tmul,
        AlgHom.toLinearMap_apply]
      apply foo
  | add sm sm' hsm hsm' =>
      simp [map_add, Pi.add_apply, Pi.single_add, tmul_add, ← hsm, ← hsm']

/- The multihomogeneous component of degree `n` of a `PolynomialLaw`. -/
@[simps] noncomputable def multiComponent (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    PolynomialLaw R (Π i, M i) N where
  toFun' S _ _ := fun m ↦ multiCoeff_S m f n
  isCompat' {S _ _} {S' _ _} φ := by
    ext sm
    apply bar

theorem multiComponent.toFun'_apply (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N)
  (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
  (f.multiComponent n).toFun' S m = multiCoeff_S m f n := rfl

-- **MI**: I replaced  `CommRing S` by `CommSemiring S` and `S : Type u` by `S : Type*`.
theorem multiComponent_toFun_apply (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N)
    (S : Type*) [CommSemiring S] [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (f.multiComponent n).toFun S m = multiCoeff_S m f n := by
  obtain ⟨n', ψ, q, rfl⟩ := exists_lift m
  rw [← PolynomialLaw.isCompat_apply, toFun_eq_toFun'_apply, multiComponent.toFun'_apply]
  exact bar n f ψ q

lemma multiComponentIsMultiHomogeneous (n : ι →₀ ℕ) (f : PolynomialLaw R (Π i, M i) N) :
    IsMultiHomogeneousOfDegree n (multiComponent n f) := by
  simp only [multiComponent]
  intro S _ _ s sm
  rw [coe_piRight_symm]
  exact multiCoeff_S_apply_smul s sm f n

theorem multiComponent_add (n : ι →₀ ℕ) (f g : PolynomialLaw R (Π i, M i) N) :
    (f + g).multiComponent n = f.multiComponent n + g.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, multiCoeff_S_apply, piRight_apply, map_sum, add_toFun_apply, map_add,
    Finsupp.coe_add, Pi.add_apply, add_def]

theorem multiComponent_smul (n : ι →₀ ℕ) (r : R) (f : PolynomialLaw R (Π i, M i) N) :
    (r • f).multiComponent n = r • f.multiComponent n := by
  ext S _ _ sm
  simp [multiComponent, multiCoeff_S_apply, piRight_apply, map_sum, smul_toFun, Pi.smul_apply,
    rTensor_apply, map_smul, smul_def]

-- Perhaps I should just use `ι →₀ ℕ` everywhere, but since I am usually assuming `Fintype ι`,
-- this seemed redundant.
-- For now, I used it in the def. of `multiComponent` to avoid this error:
/- ... has Finset (ι →₀ ℕ) : Type u but is expected to have type Set (ι → ℕ) : Type u-/
 theorem support_multiComponent' (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun' S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))).support := by
  ext n
  simp [multiComponent, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, multiCoeff_S_def]

-- **MI**: I replaced  `CommRing S` by `CommSemiring S`.
theorem support_multiComponent (f : (Π i, M i) →ₚₗ[R] N) {S : Type*} [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] (Π i, M i)) :
    Function.support (fun i => ((fun n => multiComponent n f) i).toFun S m) =
    (MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x))))))).support := by
  ext i
  rw [Function.mem_support, ne_eq, Finset.mem_coe, Finsupp.mem_support_iff, not_iff_not,
    multiComponent_toFun_apply, multiCoeff_S_def]

theorem LocFinsupp_multiComponent (f : PolynomialLaw R (Π i, M i) N) :
    LocFinsupp (fun n ↦ f.multiComponent n) := fun S _ _ m ↦ by
  rw [support_multiComponent']
  exact Finset.finite_toSet _

 theorem LocFinsupp_multiComponent_eq (f : (Π i, M i) →ₚₗ[R] N) {S : Type u} [CommSemiring S]
    [Algebra R S] (m : S ⊗[R] (Π i, M i)) :
    (Finsupp.ofSupportFinite (fun i => (multiComponent i f).toFun' S m)
      (LocFinsupp_multiComponent f S m)) =
    MvPolynomial.rTensor
      (f.toFun (MvPolynomial ι S) (∑ x,(LinearEquiv.rTensor ((i : ι) → M i)
        scalarRTensorAlgEquiv.toLinearEquiv)
          ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
            (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) m x)))))) := by
  ext n
  simp only [multiComponent, multiCoeff_S_apply, piRight_apply, map_sum, Finsupp.ofSupportFinite_coe]

open Finsupp

-- TODO: golf, extract lemmas
theorem asdf (S : Type u) [CommSemiring S] [Algebra R S] (s : S) (m : (i : ι) → M i) :
  s ⊗ₜ[R] m =
    ∑ i, (aeval 1) (scalarRTensorAlgEquiv (X i ⊗ₜ[R] s)) ⊗ₜ[R] Pi.single i (m i) := by
  by_cases hR : Nontrivial R
  · have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
    conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    simp only [rTensorAlgHom_apply_eq]

    simp only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul]
    simp only [Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    have : Finsupp.support (X (R := R) i) = {Finsupp.single i 1} := by
      rw [← support_X (R := R)]; rfl

    rw [this]
    simp only [Finset.sum_singleton, map_zero, Finsupp.prod_single_index, mul_one,
      Finsupp.sum_single_index, Algebra.TensorProduct.lid_tmul]
    have : s = (1 : R) • s := by simp only [_root_.one_smul]
    convert this
    rw [X]
    simp only [monomial, AddMonoidAlgebra.lsingle, Finsupp.lsingle, Finsupp.singleAddHom,
      ZeroHom.toFun_eq_coe, ZeroHom.coe_mk]
    change (Finsupp.single (Finsupp.single i 1) 1) (Finsupp.single i 1) = 1
    simp only [Finsupp.single_eq_same]
  · simp only [nontrivial_iff, ne_eq, not_exists, not_not] at hR
    have hm : m = ∑ i, Pi.single i (m i) := by rw [Finset.univ_sum_single m]
    conv_lhs => rw [hm, tmul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr
    simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply,
      mapAlgEquiv_apply]
    simp only [rTensorAlgHom_apply_eq]

    simp only [aeval_def, Algebra.algebraMap_self, eval₂_map, RingHomCompTriple.comp_eq]
    rw [MvPolynomial.rTensor_apply_tmul]
    simp only [Finsupp.sum]
    simp only [eval₂, RingHom.coe_coe, Pi.one_apply, one_pow]
    have : Finsupp.support (X (R := R) i) = ∅ := by
      have : Finsupp.support (X (R := R) i) = MvPolynomial.support (X (R := R) i) := by
        rw [support]
      classical rw [this, X, support_monomial, if_pos (hR 1 0)]
    rw [this]
    simp only [Finset.sum_empty, Finsupp.sum_zero_index]
    have h1 : (1 : S) = algebraMap R S 1 := by simp only [map_one]
    rw [← mul_one s, ← map_one (algebraMap R S), hR 1 0, map_zero, mul_zero]

/-- A polynomial law is the locally finite sum of its homogeneous components.
(PolynomialLaw lies in between the direct sum and the product of its graded submodules,
hence there is no graded module structure.) -/
theorem recompose_multiComponent {ι : Type u} [Fintype ι] [DecidableEq ι] {R : Type u}
  [CommSemiring R] {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module R (M i)]
  {N : Type*} [AddCommMonoid N] [Module R N]
  (f : PolynomialLaw R (Π i, M i) N) :
    PolynomialLaw.lfsum (fun n ↦ f.multiComponent n) = f := by
  ext S _ _ sm
  rw [lfsum_eq_of_locFinsupp (LocFinsupp_multiComponent f), LocFinsupp_multiComponent_eq]
  have hsm' : sm = ((aeval 1).restrictScalars R).toLinearMap.rTensor (Π i, M i) (∑ x,
    (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
      ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
        (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) sm x))))) := by
    simp only [map_sum]
    simp only [LinearMap.rTensor]
    induction sm using TensorProduct.induction_on with
    | zero =>  simp [map_zero, Pi.single_zero, tmul_zero, Finset.sum_const_zero]
    | tmul s m =>
        simp only [piRightHom_tmul, piRight_symm_single, assoc_symm_tmul]
        simp only [LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, map_tmul,
          AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', id_coe, id_eq]
        apply asdf
    | add sm₁ sm₂ hsm₁ hsm₂ => simp [map_add, Pi.add_apply, Pi.single_add, tmul_add, Finset.sum_add_distrib,
        ← hsm₁, ← hsm₂]
  conv_rhs => rw [← toFun_eq_toFun', hsm', ← f.isCompat_apply]
  generalize f.toFun (MvPolynomial ι S)
    (∑ x,
            (LinearEquiv.rTensor ((i : ι) → M i) scalarRTensorAlgEquiv.toLinearEquiv)
              ((TensorProduct.assoc R (MvPolynomial ι R) S ((i : ι) → M i)).symm
                (X x ⊗ₜ[R] (piRight R R S M).symm (Pi.single x ((piRightHom R R S M) sm x))))) = sn
  convert rTensor'_sum (R := R) (fun _ ↦ 1) sn
  · simp only [_root_.one_smul]
  · ext p
    simp only [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', aeval_eq_eval₂Hom,
      Algebra.algebraMap_self, coe_eval₂Hom, eval₂_id, eval_eq, Pi.ofNat_apply, one_pow,
      Finset.prod_const_one, mul_one, MvPolynomial.lsum, coe_restrictScalars, lsmul_apply,
      smul_eq_mul, one_mul, coe_mk, AddHom.coe_mk]
    rfl
end Components

end MultiHomogeneous

end PolynomialLaw
