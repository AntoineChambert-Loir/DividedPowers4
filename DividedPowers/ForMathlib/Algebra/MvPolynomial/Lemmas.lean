/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
import Mathlib.Algebra.BigOperators.Finsupp.Fin
import DividedPowers.ForMathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Miscellaneous lemmas and definitions for `MvPolynomial`

## Main definitions
- `MvPolynomial.baseChange` : given `φ : S →ₐ[R] S'`, `baseChange φ` aplies `φ` on the
  coefficients of a polynomial in `(MvPolynomial σ S)`.

-/

open LinearMap TensorProduct

noncomputable section

namespace MvPolynomial

section Eval

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] {σ : Type*}

variable {p q : MvPolynomial σ R} {f : R →+* S} {x : σ → S}

theorem eval₂_mul_eq_zero_of_left (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  simp [eval₂_mul f x, hp]

theorem eval₂_mul_eq_zero_of_right (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

variable (f x)

theorem eval₂_X_pow {s : σ} {n : ℕ} : ((X s) ^ n).eval₂ f x = (x s) ^ n := by
  rw [X_pow_eq_monomial, eval₂_monomial f x]
  simp

@[simp]
theorem eval₂Hom.smul (f : R →+* S) (g : σ → S) (r : R) (P : MvPolynomial σ R) :
    eval₂Hom f g (r • P) = f r • eval₂Hom f g P := by
  simp only [smul_eq_C_mul, coe_eval₂Hom, eval₂_mul, eval₂_C, smul_eq_mul]

/-- `eval₂` as an `AddMonoidHom`. -/
@[simps]
def eval₂AddMonoidHom (f : R →+* S) (g : σ → S) :
    (MvPolynomial σ R) →+ S where
  toFun := eval₂ f g
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _

/-- `eval₂` as a `RingHom`. -/
def eval₂RingHom (f : R →+* S) (g : σ → S) : (MvPolynomial σ R) →+* S :=
  { eval₂AddMonoidHom f g with
    map_one' := eval₂_one _ _
    map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]
theorem coe_eval₂RingHom (f : R →+* S) (g : σ → S) : ⇑(eval₂RingHom f g) = eval₂ f g :=
  rfl

section Algebra

variable (R)

variable [Algebra R S]

/-- `MvPolynomial.eval₂ (algebraMap R S) g` as an `R`-algebra homomorphism. -/
def eval₂AlgHom (g : σ → S) : MvPolynomial σ R →ₐ[R] S :=
  { eval₂Hom (algebraMap R S) g with
    commutes' := fun r => by rw [RingHom.toFun_eq_coe, coe_eval₂Hom, algebraMap_eq, eval₂_C] }

variable {R}

theorem eval₂AlgHom_apply (g : σ → S) (P : MvPolynomial σ R) :
  eval₂AlgHom R g P = eval₂Hom (algebraMap R S) g P := rfl

@[simp]
theorem coe_eval₂AlgHom (g : σ → S) :
  ⇑(eval₂AlgHom R g) = eval₂ (algebraMap R S) g := rfl

@[simp]
theorem eval₂AlgHom_X' (g : σ → S) (i : σ) :
  eval₂AlgHom R g (X i : MvPolynomial σ R) = g i := eval₂_X (algebraMap R S) g i

variable {S' : Type*} [CommSemiring S'] [Algebra R S']

lemma C_eq_algebraMap (r : R) :
    C (algebraMap R S r) = algebraMap R (MvPolynomial σ S) r := rfl

theorem aeval_range (s : σ → S) : (aeval s).range = Algebra.adjoin R (Set.range s) := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | C a => exact aeval_C s a ▸ Subsemiring.subset_closure (Or.inl (Set.mem_range_self a))
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p n h =>
      simp only [map_mul, aeval_X]
      exact Subalgebra.mul_mem _ h (Algebra.subset_adjoin (Set.mem_range_self n))
  · rw [Algebra.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    use X i, by aesop

end Algebra

open Ideal.Quotient

theorem mkₐ_eq_aeval {C : Type*} [CommRing C] {D : Type*} (I : Ideal (MvPolynomial D C)) :
    Ideal.Quotient.mkₐ C I = aeval fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d
  simp only [mkₐ_eq_mk, aeval_X]

theorem mk_eq_eval₂ {C : Type*} [CommRing C] {D : Type*} (I : Ideal (MvPolynomial D C)) :
    (Ideal.Quotient.mk I).toFun =
      eval₂ (algebraMap C (MvPolynomial D C ⧸ I)) fun d : D => Ideal.Quotient.mk I (X d) := by
  ext d
  simp_rw [RingHom.toFun_eq_coe, ← mkₐ_eq_mk C, mkₐ_eq_aeval, aeval_X]
  rfl

end Eval

section BaseChange

variable {R S S' σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring S']
  [Algebra R S']

/-- `baseChange φ` aplies `φ` on the coefficients of a polynomial in `(MvPolynomial σ S)`. -/
noncomputable def baseChange (φ : S →ₐ[R] S') : MvPolynomial σ S →ₐ[R] MvPolynomial σ S' where
  toRingHom := eval₂Hom (C.comp φ) X
  commutes' := fun r ↦ by simp

lemma coeff_baseChange_apply (φ : S →ₐ[R] S') (f : MvPolynomial σ S) (n : σ →₀ ℕ) :
    coeff n (baseChange φ f) = φ (coeff n f) := by
  classical
  rw [baseChange, AlgHom.coe_mk, coe_eval₂Hom]
  induction f using MvPolynomial.induction_on generalizing n with
  | C r =>
    simp [apply_ite φ]
  | add f g hf hg => simp [hf, hg]
  | mul_X q s h =>
    simp only [eval₂_mul, eval₂_X, coeff_mul, map_sum, map_mul]
    exact Finset.sum_congr rfl (fun k _ ↦ by simp [h k.1, coeff_X'])

lemma lcoeff_comp_baseChange_eq (φ : S →ₐ[R] S') (p : σ →₀ ℕ) :
    LinearMap.comp (AlgHom.toLinearMap φ) ((lcoeff S p).restrictScalars R) =
      LinearMap.comp ((lcoeff S' p).restrictScalars R) (baseChange φ).toLinearMap := by
  ext f; simp [coeff_baseChange_apply]

lemma baseChange_monomial (φ : S →ₐ[R] S') (n : σ →₀ ℕ) (a : S) :
    (baseChange φ) ((MvPolynomial.monomial n) a) = (MvPolynomial.monomial n) (φ a) := by
  simp only [baseChange, AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply]
  rw [monomial_eq]

theorem baseChange_comp_monomial_eq (φ : S →ₐ[R] S') (n : σ →₀ ℕ) :
    (MvPolynomial.baseChange φ).toLinearMap ∘ₗ ((monomial n).restrictScalars R) =
      ((monomial n).restrictScalars R) ∘ₗ φ.toLinearMap := by ext; simp [baseChange_monomial]

theorem baseChange_comp_scalarRTensorAlgEquiv_tmul [DecidableEq σ] {M : σ → Type*}
    [(i : σ) → AddCommMonoid (M i)] [(i : σ) → Module R (M i)] (φ : S →ₐ[R] S') (s : S)
    (m : (i : σ) → M i) (i : σ) :
    ((MvPolynomial.baseChange φ).toLinearMap ∘ₗ scalarRTensorAlgEquiv.toLinearMap)
      (X i ⊗ₜ[R] s) ⊗ₜ[R] Pi.single i (m i) =
      scalarRTensorAlgEquiv (X i ⊗ₜ[R] φ s) ⊗ₜ[R] Pi.single i (m i) := by
  simp only [baseChange, eval₂Hom_eq_bind₂, coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply, AlgHom.coe_mk, ← bind₂_map, bind₂_C_left,
    RingHomCompTriple.comp_apply]
  congr
  simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  ext d
  simp [rTensorAlgEquiv_apply, coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, Algebra.TensorProduct.lid_tmul, map_smul]

theorem baseChange_comp_scalarRTensorAlgEquiv_tmul_fst {M M' : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] (φ : S →ₐ[R] S') (s : S) (m : M × M') :
    ((MvPolynomial.baseChange φ).toLinearMap ∘ₗ scalarRTensorAlgEquiv.toLinearMap)
      (X (0 : Fin 2) ⊗ₜ[R] s) ⊗ₜ[R] (m.1, (0 : M')) =
      scalarRTensorAlgEquiv (X (0 : Fin 2) ⊗ₜ[R] φ s) ⊗ₜ[R] (m.1, (0 : M')) := by
  simp only [baseChange, eval₂Hom_eq_bind₂, coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply, AlgHom.coe_mk, ← bind₂_map, bind₂_C_left,
    RingHomCompTriple.comp_apply]
  congr
  simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  ext d
  simp [rTensorAlgEquiv_apply, coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, Algebra.TensorProduct.lid_tmul, map_smul]

theorem baseChange_comp_scalarRTensorAlgEquiv_tmul_snd {M M' : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M'] (φ : S →ₐ[R] S') (s : S) (m : M × M') :
    ((MvPolynomial.baseChange φ).toLinearMap ∘ₗ scalarRTensorAlgEquiv.toLinearMap)
      (X (1 : Fin 2) ⊗ₜ[R] s) ⊗ₜ[R] ((0 : M), m.2) =
      scalarRTensorAlgEquiv (X (1 : Fin 2) ⊗ₜ[R] φ s) ⊗ₜ[R] ((0 : M), m.2) := by
  simp only [baseChange, eval₂Hom_eq_bind₂, coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgEquiv.toLinearMap_apply, AlgHom.coe_mk, ← bind₂_map, bind₂_C_left,
    RingHomCompTriple.comp_apply]
  congr
  simp only [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, mapAlgEquiv_apply, map_map]
  ext d
  simp [rTensorAlgEquiv_apply, coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_comp,
    RingHom.coe_coe, Function.comp_apply, Algebra.TensorProduct.lid_tmul, map_smul]

end BaseChange

section sum

open Finsupp

variable {ι R A M : Type*} [Semiring R] [CommSemiring A] [AddCommMonoid M]
  [Module R A] [Module R M] {p q : MvPolynomial ι A}

theorem sum_add_index [DecidableEq ι] {f : (ι →₀ ℕ) → A → M}
    (hf : ∀ i ∈ p.support ∪ q.support, f i 0 = 0)
    (h_add : ∀ i ∈ p.support ∪ q.support, ∀ (b₁ b₂ : A), f i (b₁ + b₂) = f i b₁ + f i b₂) :
    (p + q).sum f = p.sum f + q.sum f := Finsupp.sum_add_index hf h_add

theorem sum_eq_of_subset {f : (ι →₀ ℕ) → A → M} (hf : ∀ (i : ι →₀ ℕ), f i 0 = 0)
    {s : Finset (ι →₀ ℕ)} (hs : p.support ⊆ s) : p.sum f = ∑ n ∈ s, f n (p.coeff n) :=
  Finsupp.sum_of_support_subset _ hs f (fun i _ ↦ hf i)

/-- Given `f : (ι →₀ ℕ) → A →ₗ[R] M`, `lsum f` is the `R`-linear map sending `p: MvPolynomial ι A`
to `p.sum (f · ·)`. -/
@[simps]
def lsum (f : (ι →₀ ℕ) → A →ₗ[R] M) : MvPolynomial ι A →ₗ[R] M where
  toFun p := p.sum (f · ·)
  map_add' p q := by
    classical
    exact MvPolynomial.sum_add_index (fun n _ => (f n).map_zero)
      (fun n _ _ _ => (f n).map_add _ _)
  map_smul' c p := by
    rw [sum_eq_of_subset (fun n => (f n).map_zero) support_smul]
    simp [sum_def, Finset.smul_sum, coeff_smul]

theorem rTensor'_sum [DecidableEq ι] {S N : Type*} [CommSemiring S] [Algebra A S] [AddCommMonoid N]
    [Module A N]
    (φ : (ι →₀ ℕ) → S) (sXn : (MvPolynomial ι S) ⊗[A] N) :
    (rTensor (R := A) (N := N) (S := S) sXn).sum (fun p sn ↦ (φ p) • sn) =
      (lsum (fun n ↦ (LinearMap.lsmul S S (φ n)).restrictScalars A)).rTensor N sXn := by
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

end sum

theorem prod_X_pow_eq_monomial' {R σ : Type*} [Fintype σ]
    {s : σ →₀ ℕ} [CommSemiring R] : ∏ x, X (R := R) x ^ s x = (monomial s) 1 := by
  rw [← prod_X_pow_eq_monomial]
  apply Finset.prod_congr_of_eq_on_inter _ (fun _ _ ha ↦ absurd (Finset.mem_univ _) ha)
    (fun _ _ _ ↦ rfl )
  intro _ _ ha
  rw [Finsupp.mem_support_iff, not_not] at ha
  rw [ha, pow_zero]

theorem nontrivial_iff_nontrivial (ι R : Type*) [CommSemiring R] :
    Nontrivial R ↔ Nontrivial (MvPolynomial ι R) := by
  refine ⟨fun h ↦ nontrivial_of_nontrivial ι R, ?_⟩
  contrapose
  intro hR
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  intro p q
  ext d
  apply hR

variable (R : Type*) [CommSemiring R]

theorem X_pow_mul_X_pow_eq_prod (e : ℕ × ℕ) :
    X (R := R) 0 ^ e.1 * X 1 ^ e.2 = ∏ i, X i ^ (finTwoArrowEquiv' ℕ).symm e i := by
  simp

theorem X_pow_mul_X_pow_eq_prod' (e : Fin 2 → ℕ) :
    X (R := R) 0 ^ e 0 * X 1 ^ e 1 = ∏ i, X i ^ e i := by
  simp

variable {R}

lemma coeff_scalarRTensorAlgEquiv {σ S : Type*} [DecidableEq σ] [CommSemiring S]
    [Algebra R S] (p : MvPolynomial σ R) (s : S) (k : σ →₀ ℕ) :
    MvPolynomial.coeff k (scalarRTensorAlgEquiv (p ⊗ₜ[R] s)) = (MvPolynomial.coeff k p) • s := by
  simp [scalarRTensorAlgEquiv, AlgEquiv.trans_apply, rTensorAlgEquiv_apply, mapAlgEquiv_apply,
    coeff_map, coeff_rTensorAlgHom_tmul, RingHom.coe_coe, Algebra.TensorProduct.lid_tmul]

@[simps! apply]
def CAlgHom {A σ : Type*} [CommSemiring A] [Algebra R A] :
    A →ₐ[R] MvPolynomial σ A where
  toRingHom := C
  commutes' _ := rfl

/-- An isomorphism between a type `ι` and the direct sum `s.compl ⊕ s`, for `s : Set ι`. -/
def _root_.Set.complSumSelfEquiv {ι : Type*} (s : Set ι) [∀ x, Decidable (x ∈ s)] :
    ι ≃ s.compl ⊕ s  where
  toFun x := if hx : x ∈ s then Sum.inr ⟨x, hx⟩ else Sum.inl ⟨x, hx⟩
  invFun x := by rcases x with (x | x) <;> exact (x : ι)
  right_inv x := by
    rcases x with (x | x)
    · simp only [Subtype.coe_eta, dite_eq_right_iff, reduceCtorEq, imp_false]
      exact x.2
    · simp only [Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
  left_inv x := by by_cases hx : x ∈ s <;> simp [hx]

/-- The polynomial ring `R[(X_i)_{i : ι}]` is isomorphic to
  `R[(X_i)_{i ∈ s.compl}][(X_i)_{i ∈ s}]`. -/
def splitAlgEquiv {ι : Type*} (s : Set ι) [∀ x, Decidable (x ∈ s)] :
    (MvPolynomial ι R) ≃ₐ[R] MvPolynomial (s.compl) (MvPolynomial (s) R) :=
  (renameEquiv R s.complSumSelfEquiv).trans (sumAlgEquiv R s.compl s)

-- PR to Mathlib.Data.Finsupp.Basic
theorem _root_.Finsupp.prod_mul_prod_compl {ι M N : Type*} [Zero M] [CommMonoid N] (s : Set ι)
   [DecidablePred (fun x ↦ x ∈ s)] (f : ι →₀ M) (g : ι → M → N) (gs : Subtype s → M → N)
   (gs' : Subtype s.compl → M → N) (hs : ∀ x : s, g x = gs x) (hs' : ∀ x : s.compl, g x = gs' x) :
   ((Finsupp.subtypeDomain s f).prod gs) *
     ((Finsupp.subtypeDomain s.compl f).prod gs') = Finsupp.prod f g := by
  classical
  simp only [Finsupp.prod]
  rw [← Finset.prod_attach f.support, ← Finset.prod_coe_sort_eq_attach, ← Finset.prod_mul_prod_compl
    (s := Finset.univ.filter (fun (x : {x // x ∈ f.support}) ↦ x.val ∈ s))]
  apply congr_arg₂
  · simp only [Finsupp.support_subtypeDomain, Finsupp.subtypeDomain_apply, Finset.univ_eq_attach]
    rw [Finset.prod_bij'
      (i := fun x hx ↦ ⟨x.val, Finset.mem_subtype.mp hx⟩)
      (j := fun (x : f.support) (hx : x ∈ Finset.filter (fun i ↦ ↑i ∈ s) f.support.attach) ↦ by
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hx
        refine ⟨x.val, hx⟩)]
    all_goals simp [← hs]
  · simp only [Finsupp.support_subtypeDomain, Finsupp.subtypeDomain_apply,
    Finset.univ_eq_attach]
    rw [show ({x ∈ f.support.attach | ↑x ∈ s})ᶜ = {x ∈ f.support.attach | ↑x ∈ sᶜ} by ext; simp]
    rw [Finset.prod_bij'
      (i := fun x hx ↦ ⟨x.val, Finset.mem_subtype.mp hx⟩)
      (j := fun (x : f.support) (hx : x ∈ Finset.filter (fun i ↦ ↑i ∈ sᶜ) f.support.attach) ↦ by
        simp only [Finset.mem_filter, Finset.mem_attach, true_and] at hx
        refine ⟨x.val, hx⟩)]
    all_goals simp [← hs']
    intro i hi _; exact hi

lemma splitAlgEquiv_monomial {ι : Type*} (s : Set ι) [∀ x, Decidable (x ∈ s)] (k : ι →₀ ℕ) (r : R) :
    splitAlgEquiv s (monomial k r) =
      monomial (k.subtypeDomain s.compl) (monomial (k.subtypeDomain s) r) := by
  simp only [splitAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply, sumAlgEquiv_apply,
    rename_monomial, sumToIter, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Function.comp_apply]
  rw [← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.prod_equivMapDomain]
  simp only [Set.complSumSelfEquiv, Equiv.coe_fn_mk, monomial_eq, C_mul]
  simp only [C_mul', Algebra.smul_mul_assoc]
  congr
  rw [smul_eq_C_mul, map_finsuppProd]
  simp only [C_pow]
  rw [Finsupp.prod_mul_prod_compl s (M := ℕ) k
    (g := fun i e ↦ if hi : i ∈ s then
      C (σ := Subtype s.compl) (R := MvPolynomial s R) (X ⟨i, hi⟩ ^ e) else X ⟨i, hi⟩ ^ e)
    (gs := fun a b ↦ C (X (R := R) a) ^b) (gs' := fun n e ↦ X n ^ e)]
  congr
  · ext1 _; ext1 _; split_ifs with hi
    · simp; rfl
    · simp
  · intro x; ext1 e
    simp only [Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta, C_pow]
    rfl
  · intro x; simp [dif_neg (show ¬((x : ι) ∈ s) by aesop)]

lemma coeff_eq_coeff_splitAlgEquiv {ι : Type*} (s : Set ι) [∀ x, Decidable (x ∈ s)]
    (P : MvPolynomial ι R) (k : ι →₀ ℕ) :
    P.coeff k = MvPolynomial.coeff (k.subtypeDomain s)
      (MvPolynomial.coeff (k.subtypeDomain s.compl) (P.splitAlgEquiv s)) := by
  induction P using MvPolynomial.induction_on' with
  | monomial n r =>
    classical
    simp only [splitAlgEquiv_monomial, MvPolynomial.coeff_monomial]
    have : n = k ↔ n.subtypeDomain s = k.subtypeDomain s ∧ n.subtypeDomain s.compl =
        k.subtypeDomain s.compl := by
      simp only [Finsupp.ext_iff, Finsupp.subtypeDomain_apply, Subtype.forall, ← forall_and]
      apply forall_congr'
      intro i
      rw [← or_imp]
      simp only [Classical.imp_iff_left_iff]
      left
      exact Decidable.or_iff_not_imp_left.mpr fun a ↦ a
    by_cases hn : n = k
    · rw [if_pos hn]
      rw [this] at hn
      rw [if_pos hn.2, coeff_monomial, if_pos hn.1]
    · rw [if_neg hn]
      rw [this, and_comm, not_and] at hn
      split_ifs with hn'
      · rw [coeff_monomial, if_neg (hn hn')]
      · simp
  | add p q hp hq => simp only [coeff_add, hp, hq, map_add]

section Supported

variable (R : Type*)  [CommSemiring R] {M : Type*}

theorem vars_X_subset {R : Type*} {σ : Type*} (n : σ) [CommSemiring R] :
    (X n : MvPolynomial σ R).vars ⊆ {n} := by
  classical
  intro u
  rw [X, mem_vars, Finset.mem_singleton]
  rintro ⟨c, hc, hc'⟩
  by_contra h'
  rw [mem_support_iff, coeff_monomial, ne_eq] at hc
  by_cases h : Finsupp.single n 1 = c
  · rw [← h, Finsupp.mem_support_iff, ne_eq, Finsupp.single_apply] at hc'
    apply hc'; rw [if_neg (Ne.symm h')]
  · apply hc; rw [if_neg h]

/-- The weighted graded algebra structure on `MvPolynomial (ℕ × M) R`. -/
local instance :
    GradedAlgebra (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ)) :=
  weightedGradedAlgebra _ _

theorem variable_mem_supported {nm : ℕ × M} (hn : 0 < nm.1) :
    X nm ∈ supported R {nm : ℕ × M | 0 < nm.1} :=
  mem_supported.mpr (Set.Subset.trans (Finset.coe_subset.mpr (vars_X_subset nm))
    (Finset.coe_singleton nm ▸ Set.singleton_subset_iff.mpr hn))

/-- The map from `MvPolynomial (ℕ × M) R` to the set of polynomials supported on
  `{nm : ℕ × M | 0 < nm.1}`, sending a polynomial `P` to itself if it is supported on
  this set and to `1` otherwise. -/
def toSupported : MvPolynomial (ℕ × M) R →ₐ[R] supported R {nm : ℕ × M | 0 < nm.1} :=
  aeval fun nm : ℕ × M =>
    dite (0 < nm.1) (fun h => ⟨X nm, variable_mem_supported R h⟩) fun _ => 1

/-- The map `toSupported R` is a homogeneous morphism of graded algebras. -/
theorem toSupported_isHomogeneous :
    GAlgHom.IsHomogeneous (weightedHomogeneousSubmodule R (Prod.fst : ℕ × M → ℕ))
      (weightedHomogeneousSubmodule R Prod.fst) (_root_.id : ℕ → ℕ)
        ((Subalgebra.val _).comp (toSupported R)) := by
  have heq : aeval
    ((supported R {nm : ℕ × M | 0 < nm.fst}).val.toFun ∘
        fun nm : ℕ × M =>
          if h : 0 < nm.fst
          then ⟨X nm, variable_mem_supported R h⟩
          else 1) =
      (supported R {nm : ℕ × M | 0 < nm.fst}).val.comp (toSupported R) := by
    apply MvPolynomial.algHom_ext
    intro nm
    simp only [toSupported, AlgHom.toFun_eq_coe, Function.comp_apply, AlgHom.coe_comp, aeval_X]
  rw [← heq]
  apply GAlgHom.IsHomogeneous_aeval (MvPolynomial (ℕ × M) R)
    (weightedHomogeneousSubmodule R Prod.fst) (AddMonoidHom.id ℕ)
  · intro nm
    simp only [mem_weightedHomogeneousSubmodule, AlgHom.toFun_eq_coe, Subalgebra.coe_val,
      Function.comp_apply, AddMonoidHom.id_apply]
    split_ifs with h
    · apply isWeightedHomogeneous_X
    · simp only [not_lt, le_zero_iff] at h
      rw [h, OneMemClass.coe_one]
      apply isWeightedHomogeneous_one

variable (M)

-- [Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous]
theorem eq_finsupp_single_of_degree_one [DecidableEq M] {d : ℕ × M →₀ ℕ}
    (hd : (Finsupp.weight Prod.fst) d = 1) (hsupp : ∀ nm ∈ d.support, 0 < nm.fst) :
    ∃ m : M, Finsupp.single (1, m) 1 = d := by
  rw [Finsupp.weight_apply, Finsupp.sum] at hd
  have hnm : ∃ nm : ℕ × M, d nm • nm.fst = 1 := by
    by_contra h0
    rw [not_exists] at h0
    have hd0 : (d.support.sum fun a : ℕ × M => d a • a.fst) = 0 := by
      rw [Finset.sum_eq_zero (fun nm hnm ↦ Nat.lt_one_iff.mp <| lt_of_le_of_ne
        (hd ▸ Finset.single_le_sum (fun x _ => zero_le (d x • x.fst)) hnm) (h0 nm))]
    rw [hd0] at hd
    exact zero_ne_one hd
  obtain ⟨nm, hnm⟩ := hnm
  rw [← hnm] at hd
  simp only [smul_eq_mul, mul_eq_one] at hnm
  use nm.snd
  ext ab
  rw [Finsupp.single_apply]
  split_ifs with hab <;> rw [← hnm.2, eq_comm, Prod.mk.eta] at hab
  · rw [hab, hnm.1]
  · rw [eq_comm]
    by_contra hab'
    have hne0 : d ab * ab.fst ≠ 0 :=
      mul_ne_zero hab' (ne_of_gt (hsupp ab (Finsupp.mem_support_iff.mpr hab')))
    have hnm_mem : nm ∈ d.support := by rw [Finsupp.mem_support_iff, hnm.1]; exact one_ne_zero
    simp only [Finset.sum_eq_sum_diff_singleton_add hnm_mem, add_eq_right,
      smul_eq_mul, Finset.sum_eq_zero_iff, Finset.mem_sdiff,
      Finsupp.mem_support_iff, Finset.mem_singleton] at hd
    exact hne0 (hd ab ⟨hab', hab⟩)

end Supported

end MvPolynomial
