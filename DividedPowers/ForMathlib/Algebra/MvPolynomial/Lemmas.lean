/- Copyright ACL & MIdFF 2024 -/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.TensorProduct.MvPolynomial

open LinearMap TensorProduct

noncomputable section

namespace MvPolynomial

section baseChange

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] {σ : Type*}

variable {p q : MvPolynomial σ R} (f : R →+* S) (x : σ → S)

theorem eval₂_mul_eq_zero_of_left (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  simp [eval₂_mul f x, hp]

theorem eval₂_mul_eq_zero_of_right (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

theorem eval₂_X_pow {s : σ} {n : ℕ} : ((X s) ^ n).eval₂ f x = (x s) ^ n := by
  rw [X_pow_eq_monomial, eval₂_monomial f x]
  simp

variable [Algebra R S] {S' : Type*} [CommSemiring S'] [Algebra R S']

lemma C_eq_algebraMap (r : R) :
    C (algebraMap R S r) = algebraMap R (MvPolynomial σ S) r := rfl

/-- baseChange φ aplies φ on the coefficients of a polynomial in `(MvPolynomial σ S)`. -/
noncomputable def baseChange (φ : S →ₐ[R] S') : MvPolynomial σ S →ₐ[R] MvPolynomial σ S' where
  toRingHom := eval₂Hom (C.comp φ) X
  commutes' := fun r ↦ by simp

--@[simp]
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

--@[simp]
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

end baseChange

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

/- theorem not_nontrivial_of_not_nontrivial {ι R : Type*} [CommSemiring R]
    (hR : ¬ Nontrivial R) :
    ¬ Nontrivial (MvPolynomial ι R) := by
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  intro p q
  ext d
  apply hR -/

/- theorem support_eq_empty_of_trivial {ι : Type u_1}
  {R : Type u} [inst_2 : CommSemiring R]
  (hR : ∀ (x x_1 : R), x = x_1) (i : ι) :
  (X (R := R) i).support = ∅ := by
  classical rw [X, support_monomial, if_pos (hR 1 0)] -/

theorem nontrivial_iff_nontrivial (ι R : Type*) [CommSemiring R] :
    Nontrivial R ↔ Nontrivial (MvPolynomial ι R) := by
  refine ⟨fun h ↦ nontrivial_of_nontrivial ι R, ?_⟩
  contrapose
  intro hR
  simp only [nontrivial_iff, ne_eq, not_exists, not_not] at *
  intro p q
  ext d
  apply hR

end MvPolynomial
