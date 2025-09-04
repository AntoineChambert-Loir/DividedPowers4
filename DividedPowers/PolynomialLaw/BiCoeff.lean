import DividedPowers.PolynomialLaw.MultiCoeff
import DividedPowers.ForMathlib.Algebra.BigOperators.Finsupp.Fin

universe u

variable {R : Type u} [CommSemiring R]

section Preliminaries

open Finsupp MvPolynomial

--TODO: move or delete
-- [Mathlib.Algebra.MvPolynomial.Equiv]
theorem extracted_1_2 (e : Fin 2 →₀ ℕ) :
    X (R := R) 0 ^ e 0 * X 1 ^ e 1 = ∏ i, X i ^ e i := by
  simp [Fin.isValue, Fin.prod_univ_two]

theorem extracted_1_3 (e : ℕ × ℕ) :
    X (R := R) 0 ^ e.1 * X 1 ^ e.2 = ∏ i, X i ^ (finTwoArrowEquiv' ℕ).symm e i := by
  simp only [Fin.isValue, finTwoArrowEquiv'_symm_apply, ofSupportFinite_coe, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

end Preliminaries

namespace Module

variable {N M M' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R M']

open MvPolynomial TensorProduct

section biGenerize

/-- `biGenerize` is the `R`-linear map sending `m : M × M'` to the sum
  `X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2) : MvPolynomial (Fin 2) R ⊗[R] (M × M')`. -/
noncomputable def biGenerize :
    (M × M') →ₗ[R] MvPolynomial (Fin 2) R ⊗[R] (M × M') where
  toFun m       := X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)
  map_add' p q  := by
    simp only [Prod.fst_add, Prod.snd_add, ← Prod.mk_zero_add_mk_zero, ← Prod.zero_mk_add_zero_mk,
      tmul_add]
    abel
  map_smul' r p := by simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add,
    ← Prod.smul_mk_zero, ← Prod.smul_zero_mk, tmul_smul]

theorem biGenerize_eq_generize (m : M × M') :
    (biGenerize m) = (generize (R := R) (![(m.1, 0), (0, m.2)])) := by
  simp [generize, biGenerize]

end biGenerize

end Module

/- # Polynomial laws. -/

namespace PolynomialLaw

open Finset LinearMap MvPolynomial TensorProduct

/- ## Coefficients of polynomial laws. -/

section Coefficients

variable {N M M' : Type*} [AddCommMonoid N] [Module R N] [AddCommMonoid M]
  [Module R M] [AddCommMonoid M'] [Module R M']

section biCoeff

variable (m : M × M') (f : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ)

/-- Given `m : M × M'`, `biGenerize' m` is the `R`-linear map sending
`f : (M × M') →ₚₗ[R] N` to the term of `MvPolynomial (Fin 2) R ⊗[R] N` obtained by applying
`f.toFun (MvPolynomial (Fin 2) R)` to the sum `X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)`.
This is provided as an auxiliary map for the definition `PolynomialLaw.biCoeff`. -/
noncomputable def biGenerize' :
    ((M × M') →ₚₗ[R] N) →ₗ[R] MvPolynomial (Fin 2) R ⊗[R] N where
  toFun f       := f.toFun (MvPolynomial (Fin 2) R) (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2))
  map_add' p q  := by simp [add_toFun_apply]
  map_smul' r p := by simp [RingHom.id_apply, smul_toFun, Pi.smul_apply]

private noncomputable def biCoeff_aux : N :=
  scalarRTensor.toLinearMap.comp (biGenerize' m) f ((finTwoArrowEquiv' ℕ).symm n)

private lemma biCoeff_aux_apply :
  biCoeff_aux m f n = scalarRTensor.toLinearMap.comp (biGenerize' m) f
      ((finTwoArrowEquiv' ℕ).symm n) := rfl

private lemma finite_support_biCoeff_aux :
    (Function.support (biCoeff_aux m f)).Finite := by
  apply Set.Finite.of_injOn (f := (finTwoArrowEquiv' ℕ).symm) ?_
    (Equiv.injective (finTwoArrowEquiv' ℕ).symm).injOn (Finsupp.finite_support
    (scalarRTensor.toLinearMap.comp (biGenerize' m) f))
  simp only [Set.MapsTo, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Function.mem_support,
    ne_eq, Finsupp.fun_support_eq, mem_coe, Finsupp.mem_support_iff, Prod.forall]
  exact fun _ _ hab ↦ by simpa using hab

/-- The b-coefficients of a `PolynomialLaw`, as linear maps. -/
noncomputable def biCoeff : ((M × M') →ₚₗ[R] N) →ₗ[R] (ℕ × ℕ) →₀ N where
  toFun g := Finsupp.ofSupportFinite (fun n ↦ scalarRTensor.toLinearMap.comp (biGenerize' m) g
      ((finTwoArrowEquiv' ℕ).symm n)) (finite_support_biCoeff_aux m g)
  map_add' mn mn' := by simp [Finsupp.ext_iff, Finsupp.ofSupportFinite_coe]
  map_smul' r nm := by simp [Finsupp.ext_iff, Finsupp.ofSupportFinite_coe]

open Module

private theorem coeff_support_finite : (Function.support fun n ↦
    ((coeff ![(m.1, 0), (0, m.2)]) f) ((finTwoArrowEquiv' ℕ).symm n)).Finite :=
  Set.Finite.of_injOn (f := (finTwoArrowEquiv' ℕ).symm) (by simp [Set.MapsTo]) (Equiv.injective
    (finTwoArrowEquiv' ℕ).symm).injOn (Finsupp.finite_support (coeff ![(m.1, 0), (0, m.2)] f))

theorem biCoeff_eq_coeff : biCoeff m f = Finsupp.ofSupportFinite
    (fun n ↦ coeff ![(m.1, 0), (0, m.2)] f ((finTwoArrowEquiv' ℕ).symm n))
      (coeff_support_finite m f) := by
  simp [biCoeff, biGenerize', coeff, generize', generize, coe_mk, AddHom.coe_mk]

theorem biCoeff_apply_eq_coeff_apply :
    biCoeff m f n = coeff ![(m.1, 0), (0, m.2)] f ((finTwoArrowEquiv' ℕ).symm n) := by
  simp [biCoeff_eq_coeff, Finsupp.ofSupportFinite_coe]

-- TODO: move
theorem _root_.Finsupp.ofSupportFinite_fin_two_eq (n : Fin 2 →₀ ℕ) :
    Finsupp.ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

theorem toFun_biGenerize_eq : f.toFun (MvPolynomial (Fin 2) R) (biGenerize m) =
    (biCoeff m f).sum (fun k n ↦ (monomial ((finTwoArrowEquiv' ℕ).symm k) 1) ⊗ₜ n) := by
  simp only [biGenerize_eq_generize, Nat.succ_eq_add_one, Nat.reduceAdd, toFun_generize_eq,
    finTwoArrowEquiv'_symm_apply]
  simp only [Finsupp.sum, biCoeff_apply_eq_coeff_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    finTwoArrowEquiv'_symm_apply]
  apply Finset.sum_bij (fun n _ ↦ finTwoArrowEquiv' ℕ n) _ _ _
    (fun _ _ ↦ by simp [Finsupp.ofSupportFinite_fin_two_eq])
  · intro _ hn
    simpa [biCoeff_apply_eq_coeff_apply, Finsupp.ofSupportFinite_fin_two_eq] using hn
  · intro _ _ _ _ h
    simpa [Finsupp.ext_iff, Fin.forall_fin_two] using h
  · intro n hn
    exact ⟨(finTwoArrowEquiv' ℕ).symm n, by simpa [biCoeff_eq_coeff] using hn,
      by simp only [Equiv.apply_symm_apply]⟩

lemma biCoeff_apply (g : (M × M') →ₚₗ[R] N) (n : ℕ × ℕ) :
    biCoeff m g n =
      scalarRTensor.toLinearMap.comp (biGenerize' m) g ((finTwoArrowEquiv' ℕ).symm n) := rfl

theorem biCoeff_eq :
  biCoeff m f n = (TensorProduct.lid R N) ((LinearMap.rTensor N (MvPolynomial.lcoeff R
    ((finTwoArrowEquiv' ℕ).symm n)))
      (f.toFun (MvPolynomial (Fin 2) R) (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2)))) := by
  simp only [biCoeff, coe_comp, LinearEquiv.coe_coe, Function.comp_apply, coe_mk, AddHom.coe_mk,
    Fin.isValue]
  exact scalarRTensor_apply _ _

theorem toFun_add_tmul_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r s : S) :
    f.toFun S (r ⊗ₜ[R] (m.1, 0) + s ⊗ₜ (0, m.2)) =
      (biCoeff m f).sum (fun k n ↦ (r ^ k.1 * s ^ k.2) ⊗ₜ[R] n) := by
  have this := congr_fun (f.isCompat (MvPolynomial.aeval ((finTwoArrowEquiv' S).symm (r, s))))
     (X 0 ⊗ₜ[R] (m.1, 0) + X 1 ⊗ₜ[R] (0, m.2))
  simp only [Fin.isValue, Function.comp_apply, map_add, rTensor_tmul, AlgHom.toLinearMap_apply,
    aeval_X] at this
  simp only [finTwoArrowEquiv', Fin.isValue, Equiv.coe_fn_symm_mk, Finsupp.ofSupportFinite_coe,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  let h := toFun_biGenerize_eq m f
  simp only [biGenerize, coe_mk, AddHom.coe_mk] at h
  rw [← this, h, Finsupp.sum, _root_.map_sum]
  apply sum_congr rfl
  intro k _
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
  apply congr_arg₂ _ _ rfl
  simp [aeval_monomial, _root_.map_one, Finsupp.prod_pow, one_mul, finTwoArrowEquiv',
    Finsupp.ofSupportFinite_coe ]

theorem toFun_tmul_fst_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) :
    f.toFun S (r ⊗ₜ[R] (m.1, 0)) =
      ((biCoeff (m.1, 0) f).sum fun k n ↦ (r ^ k.1 * r ^ k.2) ⊗ₜ[R] n) := by
  have : r ⊗ₜ[R] (m.1, (0 : M')) = (r, r).1 ⊗ₜ[R] (m.1, 0) + (r, r).2 ⊗ₜ[R] (0, 0) := by
    simp [Prod.mk_zero_zero, tmul_zero, add_zero]
  rw [this, toFun_add_tmul_eq_biCoeff_sum (m.1, 0)]

theorem toFun_tmul_snd_eq_biCoeff_sum (S : Type*) [CommSemiring S] [Algebra R S] (r : S) :
    f.toFun S (r ⊗ₜ[R] (0, m.2)) =
      ((biCoeff (0, m.2) f).sum fun k n ↦ (r ^ k.1 * r ^ k.2) ⊗ₜ[R] n) := by
  have : r ⊗ₜ[R] ((0 : M), m.2) = (r, r).1 ⊗ₜ[R] (0, 0) + (r, r).2 ⊗ₜ[R] (0, m.2) := by
    simp [Prod.mk_zero_zero, tmul_zero, zero_add]
  rw [this, toFun_add_tmul_eq_biCoeff_sum (0, m.2)]

end biCoeff

open Function

variable (r : R × R) (r₁ r₂ : R) (m m₁ m₂ : M × M') (k : ℕ × ℕ) (f : (M × M') →ₚₗ[R] N)

theorem ground_apply_sum_smul_eq_biCoeff_sum :
    ground f (r.1 • (m.1, 0) + r.2 • (0, m.2)) =
      (biCoeff m f).sum (fun k n ↦ (r.1 ^ k.1 * r.2 ^ k.2) • n) := by
  apply (TensorProduct.lid R N).symm.injective
  rw [TensorProduct.lid_symm_apply, one_tmul_ground_apply', ← TensorProduct.lid_symm_apply]
  simp only [map_add, TensorProduct.lid_symm_apply, ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]
  rw [← toFun_eq_toFun', toFun_add_tmul_eq_biCoeff_sum, ← TensorProduct.lid_symm_apply]
  simp only [map_finsuppSum, TensorProduct.lid_symm_apply]
  exact Finsupp.sum_congr (fun d _ ↦ by rw [← TensorProduct.smul_tmul, smul_eq_mul, mul_one])

theorem ground_apply_smul_eq_biCoeff_sum :
    ground f (r₁ • m₁) = (biCoeff m₁ f).sum (fun k n ↦ r₁ ^ (k.1 + k.2) • n) := by
  suffices r₁ • m₁ = (r₁, r₁).1 • (m₁.1, 0) + (r₁, r₁).2 • (0, m₁.2) by
    rw [this, ground_apply_sum_smul_eq_biCoeff_sum]
    exact sum_congr rfl (by simp [pow_add])
  simp only [← smul_add, Prod.mk_add_mk, add_zero, zero_add]

variable {S : Type*} [CommSemiring S] [Algebra R S] {m}

theorem biCoeff_injective
    (hm : Submodule.span R (Set.range ![(m.1, (0 : M')), ((0 : M), m.2)]) = ⊤) :
    Function.Injective (biCoeff m : ((M × M') →ₚₗ[R] N) →ₗ[R] (ℕ × ℕ) →₀ N) := fun f g h ↦ by
  simp only [biCoeff_eq_coeff, Nat.succ_eq_add_one, Nat.reduceAdd, finTwoArrowEquiv'_symm_apply,
    Finsupp.ext_iff, Finsupp.ofSupportFinite_coe, Prod.forall] at h
  apply coeff_injective hm
  ext n
  simpa [Finsupp.ofSupportFinite_fin_two_eq] using h (n 0) (n 1)

theorem biCoeff_inj (hm : Submodule.span R (Set.range ![(m.1, (0 : M')), ((0 : M), m.2)]) = ⊤)
    {f g : (M × M') →ₚₗ[R] N} :
    (biCoeff m f) = (biCoeff m g ) ↔ f = g := (biCoeff_injective hm).eq_iff

end Coefficients

end PolynomialLaw
